/-
  PriorityRanking.Basic
  Core types, prefix sums, coverage sets, and helper lemmas for the
  axiomatization of priority-based ranking rules.

  Paper reference: "Axiomatizations of Priority-Based Ranking Rules"
  (Eduardo Zambrano)

  Convention: The paper uses 1-based indexing (state 1 = highest priority).
  Lean uses 0-based indexing via Fin n (state 0 = highest priority).
-/

import Mathlib.Tactic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.SymmDiff

open Finset
open scoped symmDiff

/-! ## Core types -/

/-- A vector of real-valued payoffs across `n` priority-ordered states. -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- A nonnegative vector (the primary domain in the paper). -/
def NNVec (n : ℕ) := { v : Vec n // ∀ i, 0 ≤ v i }

/-- A preference relation (weak) on vectors. `R x y` means "x is weakly preferred to y". -/
def PrefRel (n : ℕ) := Vec n → Vec n → Prop

/-- The strict part of a preference relation: x is strictly preferred to y. -/
def strictPart {n : ℕ} (R : PrefRel n) (x y : Vec n) : Prop :=
  R x y ∧ ¬ R y x

/-- The indifference part: x and y are indifferent. -/
def indiffPart {n : ℕ} (R : PrefRel n) (x y : Vec n) : Prop :=
  R x y ∧ R y x

/-! ## Prefix sums -/

/-- Prefix sum: S_j(x) = sum of x_i for i in {0, 1, ..., j}.
    In the paper's notation with 1-based indexing, this is S_{j+1}(x). -/
noncomputable def prefixSum {n : ℕ} (x : Vec n) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.Iic j, x i

/-- The prefix-sum vector: maps each index to its prefix sum. -/
noncomputable def prefixVec {n : ℕ} (x : Vec n) : Vec n :=
  fun j => prefixSum x j

/-- Total sum: S_n(x) = sum of all coordinates. -/
noncomputable def totalSum {n : ℕ} (x : Vec n) : ℝ :=
  ∑ i, x i

/-- Prefix sum at index 0 equals the first coordinate. -/
theorem prefixSum_zero {n : ℕ} (x : Vec n) (h : 0 < n) :
    prefixSum x ⟨0, h⟩ = x ⟨0, h⟩ := by
  simp only [prefixSum]
  have : Iic (⟨0, h⟩ : Fin n) = {⟨0, h⟩} := by
    ext ⟨i, hi⟩; simp only [mem_Iic, Fin.le_iff_val_le_val, mem_singleton, Fin.ext_iff]; omega
  rw [this, Finset.sum_singleton]

/-! ### Prefix sum decomposition -/

/-- Prefix sum decomposition: S_{k+1}(x) = S_k(x) + x_{k+1}. -/
theorem prefixSum_succ {n : ℕ} (x : Vec n) (k : ℕ) (hk1 : k + 1 < n) (hk : k < n) :
    prefixSum x ⟨k + 1, hk1⟩ = prefixSum x ⟨k, hk⟩ + x ⟨k + 1, hk1⟩ := by
  simp only [prefixSum]
  have hdecomp : Iic (⟨k + 1, hk1⟩ : Fin n) = Iic (⟨k, hk⟩ : Fin n) ∪ {⟨k + 1, hk1⟩} := by
    ext ⟨i, hi⟩
    simp only [mem_Iic, Fin.le_iff_val_le_val, mem_union, mem_singleton, Fin.ext_iff]
    omega
  have hdisj : Disjoint (Iic (⟨k, hk⟩ : Fin n)) ({⟨k + 1, hk1⟩} : Finset (Fin n)) := by
    simp only [Finset.disjoint_singleton_right, mem_Iic, Fin.le_iff_val_le_val, not_le]
    omega
  rw [hdecomp, Finset.sum_union hdisj, Finset.sum_singleton]

/-- Total sum equals prefix sum at the last index. -/
theorem totalSum_eq_prefixSum_last {n : ℕ} [NeZero n] (x : Vec n) :
    totalSum x = prefixSum x ⟨n - 1, Nat.sub_one_lt_of_le (NeZero.pos n) le_rfl⟩ := by
  have hn := NeZero.pos n
  simp only [totalSum, prefixSum]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  have : Iic (⟨n - 1, by omega⟩ : Fin n) = Finset.univ := by
    ext ⟨i, hi⟩; constructor
    · intro _; exact mem_univ _
    · intro _; exact mem_Iic.mpr (Fin.mk_le_mk.mpr (by omega))
  exact this.symm

/-! ### Prefix sum lemmas -/

theorem prefixSum_eq_of_coord_eq {n : ℕ} (x y : Vec n) (j : Fin n)
    (h : ∀ i : Fin n, i ≤ j → x i = y i) :
    prefixSum x j = prefixSum y j := by
  simp only [prefixSum]
  apply Finset.sum_congr rfl
  intro i hi
  exact h i (Finset.mem_Iic.mp hi)

/-- If all coordinates are nonneg, prefix sums are nondecreasing. -/
theorem nonneg_prefixSum_mono {n : ℕ} (x : Vec n) (hx : ∀ i, 0 ≤ x i)
    (i j : Fin n) (hij : i ≤ j) :
    prefixSum x i ≤ prefixSum x j := by
  simp only [prefixSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Iic_subset_Iic.mpr hij
  · intro k _ _
    exact hx k

/-- If all prefix sums agree, then all coordinates agree. -/
theorem eq_of_prefixSum_eq {n : ℕ} (x y : Vec n)
    (h : ∀ j : Fin n, prefixSum x j = prefixSum y j) :
    x = y := by
  funext ⟨i, hi⟩
  induction i with
  | zero =>
    have h0 := h ⟨0, hi⟩
    simp only [prefixSum] at h0
    have hIic : Finset.Iic (⟨0, hi⟩ : Fin n) = {⟨0, hi⟩} := by
      ext ⟨k, hk⟩
      simp only [Finset.mem_Iic, Fin.le_iff_val_le_val, Finset.mem_singleton, Fin.ext_iff]
      omega
    rw [hIic] at h0; simpa using h0
  | succ k _ =>
    -- x_{k+1} = S_{k+1}(x) - S_k(x), same for y; since S's agree, coords agree
    have hk : k < n := by omega
    have hsx := prefixSum_succ x k hi hk
    have hsy := prefixSum_succ y k hi hk
    linarith [h ⟨k + 1, hi⟩, h ⟨k, hk⟩]

/-! ## Coverage sets -/

/-- Coverage set: H_a(x) = {i : Fin n | a ≤ x i}.
    Uses classical decidability since ℝ inequalities are not computably decidable. -/
noncomputable def coverageSet {n : ℕ} (x : Vec n) (a : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a ≤ x i)

theorem mem_coverageSet {n : ℕ} (x : Vec n) (a : ℝ) (i : Fin n) :
    i ∈ coverageSet x a ↔ a ≤ x i := by
  simp [coverageSet]

/-- Symmetric difference of coverage sets. -/
noncomputable def coverageSymmDiff {n : ℕ} (x y : Vec n) (a : ℝ) : Finset (Fin n) :=
  (coverageSet x a) ∆ (coverageSet y a)

/-! ## Threshold values -/

/-- The set of coordinate values appearing in x or y. These are the only
    thresholds at which coverage sets can change. -/
noncomputable def thresholdValues {n : ℕ} (x y : Vec n) : Finset ℝ :=
  (Finset.univ.image x) ∪ (Finset.univ.image y)

/-- Thresholds at which coverage sets of x and y differ. -/
noncomputable def differingThresholds {n : ℕ} (x y : Vec n) : Finset ℝ :=
  (thresholdValues x y).filter (fun a => coverageSet x a ≠ coverageSet y a)

/-- If x ≠ y, there exists a threshold where coverage sets differ. -/
theorem differingThresholds_nonempty {n : ℕ} (x y : Vec n) (hne : x ≠ y) :
    (differingThresholds x y).Nonempty := by
  -- x ≠ y means ∃ i, x i ≠ y i
  have ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  rcases lt_or_gt_of_ne hi with h | h
  · -- x i < y i: at threshold a = y i, i ∈ H_a(y) but i ∉ H_a(x)
    refine ⟨y i, ?_⟩
    simp only [differingThresholds, thresholdValues, Finset.mem_filter, Finset.mem_union,
      Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨Or.inr ⟨i, rfl⟩, ?_⟩
    intro heq
    have hi_in : i ∈ coverageSet y (y i) := by
      simp [coverageSet]
    rw [← heq] at hi_in
    simp [coverageSet] at hi_in
    linarith
  · -- x i > y i: at threshold a = x i, i ∈ H_a(x) but i ∉ H_a(y)
    refine ⟨x i, ?_⟩
    simp only [differingThresholds, thresholdValues, Finset.mem_filter, Finset.mem_union,
      Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨Or.inl ⟨i, rfl⟩, ?_⟩
    intro heq
    have hi_in : i ∈ coverageSet x (x i) := by
      simp [coverageSet]
    rw [heq] at hi_in
    simp [coverageSet] at hi_in
    linarith

/-- If coverage sets differ at a threshold, their symmetric difference is nonempty. -/
theorem symmDiff_nonempty_of_ne {n : ℕ} (x y : Vec n) (a : ℝ)
    (h : coverageSet x a ≠ coverageSet y a) :
    ((coverageSet x a) ∆ (coverageSet y a)).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  apply h
  ext i
  constructor
  · intro hxi
    by_contra hyi
    have : i ∈ (coverageSet x a) ∆ (coverageSet y a) := by
      rw [Finset.mem_symmDiff]
      exact Or.inl ⟨hxi, hyi⟩
    rw [hempty] at this
    simp at this
  · intro hyi
    by_contra hxi
    have : i ∈ (coverageSet x a) ∆ (coverageSet y a) := by
      rw [Finset.mem_symmDiff]
      exact Or.inr ⟨hyi, hxi⟩
    rw [hempty] at this
    simp at this

/-! ## Pareto dominance (helper) -/

/-- Componentwise ≥ with strict somewhere: x Pareto-dominates y. -/
def paretoDom {n : ℕ} (x y : Vec n) : Prop :=
  (∀ i, x i ≥ y i) ∧ (∃ j, x j > y j)

/-- Componentwise ≥ (weak Pareto). -/
def paretoWeak {n : ℕ} (x y : Vec n) : Prop :=
  ∀ i, x i ≥ y i

/-! ## FOSD -/

/-- x weakly FOSD-dominates y: all prefix sums of x are ≥ those of y. -/
def fosdWeak {n : ℕ} (x y : Vec n) : Prop :=
  ∀ j : Fin n, prefixSum x j ≥ prefixSum y j

/-- x strictly FOSD-dominates y: weak FOSD plus strict at some index. -/
def fosdStrict {n : ℕ} (x y : Vec n) : Prop :=
  fosdWeak x y ∧ ∃ j : Fin n, prefixSum x j > prefixSum y j

/-- Pareto dominance implies FOSD dominance. -/
theorem paretoDom_imp_fosdStrict {n : ℕ} (x y : Vec n) (h : paretoDom x y) :
    fosdStrict x y := by
  refine ⟨fun j => ?_, ?_⟩
  · -- Weak: each prefix sum of x ≥ that of y
    simp only [prefixSum]
    apply Finset.sum_le_sum
    intro i _
    exact h.1 i
  · -- Strict: at the index j where x j > y j, prefix sum is strictly larger
    obtain ⟨j, hj⟩ := h.2
    exact ⟨j, by
      simp only [prefixSum]
      apply Finset.sum_lt_sum
      · intro i _; exact h.1 i
      · exact ⟨j, Finset.mem_Iic.mpr (le_refl j), hj⟩⟩

/-! ## Utility lemmas for Finset extrema -/

/-- min' respects set equality (proof argument is irrelevant). -/
theorem Finset.min'_of_eq {α : Type*} [LinearOrder α] {s t : Finset α}
    (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by
  subst h; rfl

/-- max' respects set equality (proof argument is irrelevant). -/
theorem Finset.max'_of_eq {α : Type*} [LinearOrder α] {s t : Finset α}
    (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.max' hs = t.max' ht := by
  subst h; rfl

/-! ## Utility lemmas for Fin arithmetic -/

/-- The successor of a Fin value, when it exists. -/
def Fin.succFin {n : ℕ} (j : Fin n) (h : j.val + 1 < n) : Fin n :=
  ⟨j.val + 1, h⟩

theorem Fin.succFin_val {n : ℕ} (j : Fin n) (h : j.val + 1 < n) :
    (Fin.succFin j h).val = j.val + 1 := rfl
