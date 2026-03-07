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

/-! ## Symmetric difference transitivity -/

/-- Elements below the min of a symmetric difference agree across both sets. -/
theorem mem_iff_of_lt_symmDiff_min' {α : Type*} [LinearOrder α] [DecidableEq α]
    {A B : Finset α} (hne : (A ∆ B).Nonempty) {r : α}
    (hr : r < (A ∆ B).min' hne) :
    r ∈ A ↔ r ∈ B := by
  constructor
  · intro ha; by_contra hb
    exact absurd (Finset.min'_le _ r (Finset.mem_symmDiff.mpr (Or.inl ⟨ha, hb⟩))) (not_le.mpr hr)
  · intro hb; by_contra ha
    exact absurd (Finset.min'_le _ r (Finset.mem_symmDiff.mpr (Or.inr ⟨hb, ha⟩))) (not_le.mpr hr)

/-- Transitivity of the "min of symmetric difference" comparison.
    If min(A △ B) ∈ A and min(B △ C) ∈ B, then (A △ C) is nonempty
    and min(A △ C) ∈ A. -/
theorem symmDiff_min_trans {α : Type*} [LinearOrder α] [DecidableEq α]
    {A B C : Finset α}
    (hAB_ne : (A ∆ B).Nonempty) (hBC_ne : (B ∆ C).Nonempty)
    (hAB : (A ∆ B).min' hAB_ne ∈ A)
    (hBC : (B ∆ C).min' hBC_ne ∈ B) :
    ∃ (h : (A ∆ C).Nonempty), (A ∆ C).min' h ∈ A := by
  set p := (A ∆ B).min' hAB_ne
  set q := (B ∆ C).min' hBC_ne
  -- p ∈ A \ B (p is in A by hypothesis, and in the symm diff, so not in B)
  have hp_mem := Finset.min'_mem _ hAB_ne
  have hp_not_B : p ∉ B := by
    rw [Finset.mem_symmDiff] at hp_mem
    rcases hp_mem with ⟨_, h⟩ | ⟨_, hna⟩
    · exact h
    · exact absurd hAB hna
  -- q ∈ B \ C
  have hq_mem := Finset.min'_mem _ hBC_ne
  have hq_not_C : q ∉ C := by
    rw [Finset.mem_symmDiff] at hq_mem
    rcases hq_mem with ⟨_, h⟩ | ⟨_, hnb⟩
    · exact h
    · exact absurd hBC hnb
  -- Helper: elements below both p and q agree between A and C
  have agree_below : ∀ r, r < p → r < q → (r ∈ A ↔ r ∈ C) :=
    fun r hrp hrq => (mem_iff_of_lt_symmDiff_min' hAB_ne hrp).trans
      (mem_iff_of_lt_symmDiff_min' hBC_ne hrq)
  -- Helper: if e ∈ A ∆ C and all elements below e agree, then min(A ∆ C) = e
  have is_min : ∀ (e : α) (he : e ∈ A ∆ C),
      (∀ r, r < e → (r ∈ A ↔ r ∈ C)) → (A ∆ C).min' ⟨e, he⟩ = e := by
    intro e he hbelow
    apply le_antisymm (Finset.min'_le _ e he)
    apply Finset.le_min'
    intro r hr
    by_contra hlt; push_neg at hlt
    have := hbelow r hlt
    rw [Finset.mem_symmDiff] at hr
    rcases hr with ⟨ha, hc⟩ | ⟨hc, ha⟩
    · exact hc (this.mp ha)
    · exact ha (this.mpr hc)
  rcases lt_trichotomy p q with hp_lt | hp_eq | hp_gt
  · -- Case p < q: p ∉ C (since p ∈ B ↔ p ∈ C by minimality and p ∉ B), so p ∈ A △ C
    have hp_not_C : p ∉ C :=
      fun h => hp_not_B ((mem_iff_of_lt_symmDiff_min' hBC_ne hp_lt).mpr h)
    have hp_in : p ∈ A ∆ C := Finset.mem_symmDiff.mpr (Or.inl ⟨hAB, hp_not_C⟩)
    refine ⟨⟨p, hp_in⟩, ?_⟩
    rw [is_min p hp_in (fun r hr => agree_below r hr (lt_trans hr hp_lt))]; exact hAB
  · -- Case p = q: p ∈ A, p ∉ B, but p = q ∈ B — contradiction
    exact absurd (hp_eq ▸ hBC) hp_not_B
  · -- Case p > q: q ∈ A (since q ∈ A ↔ q ∈ B by minimality and q ∈ B), so q ∈ A △ C
    have hq_in_A : q ∈ A := (mem_iff_of_lt_symmDiff_min' hAB_ne hp_gt).mpr hBC
    have hq_in : q ∈ A ∆ C := Finset.mem_symmDiff.mpr (Or.inl ⟨hq_in_A, hq_not_C⟩)
    refine ⟨⟨q, hq_in⟩, ?_⟩
    rw [is_min q hq_in (fun r hr => agree_below r (lt_trans hr hp_gt) hr)]; exact hq_in_A

/-! ## Coverage set stability -/

/-- Coverage sets are stable between coordinate values: if no coordinate of x
    lies in [s, t), then H_s(x) = H_t(x). -/
theorem coverageSet_stable {n : ℕ} (x : Vec n) (s t : ℝ) (hst : s ≤ t)
    (h : ∀ i : Fin n, x i < s ∨ x i ≥ t) :
    coverageSet x s = coverageSet x t := by
  ext i
  simp only [coverageSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases h i with hlt | hge
  · exact ⟨fun hs => absurd hs (not_le.mpr hlt),
          fun ht => absurd (le_trans hst ht) (not_le.mpr hlt)⟩
  · exact ⟨fun _ => hge, fun _ => le_trans hst hge⟩

/-- When we enlarge the threshold set, the coverage symmetric difference at the
    min-differing-threshold is preserved. Key lemma for transitivity of PPROT/QPROT. -/
theorem enlarged_symmDiff_eq_min {n : ℕ} (x y : Vec n)
    (S T : Finset ℝ) (hST : S ⊆ T)
    (hx : ∀ i : Fin n, x i ∈ S) (hy : ∀ i : Fin n, y i ∈ S)
    (hS_ne : (S.filter (fun a => coverageSet x a ≠ coverageSet y a)).Nonempty)
    (hT_ne : (T.filter (fun a => coverageSet x a ≠ coverageSet y a)).Nonempty) :
    coverageSymmDiff x y ((T.filter (fun a => coverageSet x a ≠ coverageSet y a)).min' hT_ne) =
    coverageSymmDiff x y ((S.filter (fun a => coverageSet x a ≠ coverageSet y a)).min' hS_ne) ∧
    coverageSet x ((T.filter (fun a => coverageSet x a ≠ coverageSet y a)).min' hT_ne) =
    coverageSet x ((S.filter (fun a => coverageSet x a ≠ coverageSet y a)).min' hS_ne) := by
  set DT_S := S.filter (fun a => coverageSet x a ≠ coverageSet y a) with hDT_S_def
  set DT_T := T.filter (fun a => coverageSet x a ≠ coverageSet y a) with hDT_T_def
  set a₁ := DT_S.min' hS_ne
  set a₀ := DT_T.min' hT_ne
  have hDT_sub : DT_S ⊆ DT_T := fun t ht =>
    Finset.mem_filter.mpr ⟨hST (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2⟩
  have ha₀_le : a₀ ≤ a₁ := Finset.min'_le _ a₁ (hDT_sub (Finset.min'_mem _ hS_ne))
  rcases eq_or_lt_of_le ha₀_le with ha_eq | ha₀_lt
  · rw [ha_eq]; exact ⟨rfl, rfl⟩
  · -- a₀ < a₁. a₀ ∉ S (otherwise it would be in DT_S, contradicting minimality of a₁).
    have ha₀_not_S : a₀ ∉ S := by
      intro h
      exact absurd (Finset.min'_le DT_S a₀ (Finset.mem_filter.mpr
        ⟨h, (Finset.mem_filter.mp (Finset.min'_mem _ hT_ne)).2⟩)) (not_le.mpr ha₀_lt)
    have hx_ne : ∀ i, x i ≠ a₀ := fun i h => ha₀_not_S (h ▸ hx i)
    have hy_ne : ∀ i, y i ≠ a₀ := fun i h => ha₀_not_S (h ▸ hy i)
    -- Next S-value above a₀
    set S_above := S.filter (fun t => a₀ < t) with hS_above_def
    have hS_above_ne : S_above.Nonempty :=
      ⟨a₁, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.min'_mem _ hS_ne)).1, ha₀_lt⟩⟩
    set s := S_above.min' hS_above_ne
    have hs_gt : a₀ < s := (Finset.mem_filter.mp (Finset.min'_mem _ hS_above_ne)).2
    have hs_le : s ≤ a₁ :=
      Finset.min'_le _ a₁ (Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.min'_mem _ hS_ne)).1, ha₀_lt⟩)
    -- Coverage stable: no x_i or y_i in [a₀, s), so H_{a₀} = H_s
    have hcov_x : coverageSet x a₀ = coverageSet x s := by
      apply coverageSet_stable _ _ _ (le_of_lt hs_gt)
      intro i; rcases lt_or_ge (x i) a₀ with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.min'_le _ (x i) (Finset.mem_filter.mpr
          ⟨hx i, lt_of_le_of_ne h (Ne.symm (hx_ne i))⟩))
    have hcov_y : coverageSet y a₀ = coverageSet y s := by
      apply coverageSet_stable _ _ _ (le_of_lt hs_gt)
      intro i; rcases lt_or_ge (y i) a₀ with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.min'_le _ (y i) (Finset.mem_filter.mpr
          ⟨hy i, lt_of_le_of_ne h (Ne.symm (hy_ne i))⟩))
    -- s must equal a₁ (if s < a₁, coverage agrees at s, propagating to a₀ — contradiction)
    have hs_eq : s = a₁ := by
      rcases eq_or_lt_of_le hs_le with h | h
      · exact h
      · exfalso
        have hs_S : s ∈ S := (Finset.mem_filter.mp (Finset.min'_mem _ hS_above_ne)).1
        have : coverageSet x s = coverageSet y s := by
          by_contra hne_s
          exact absurd (Finset.min'_le _ s (Finset.mem_filter.mpr ⟨hs_S, hne_s⟩))
            (not_le.mpr h)
        exact (Finset.mem_filter.mp (Finset.min'_mem _ hT_ne)).2
          (by rw [hcov_x, hcov_y, this])
    rw [hs_eq] at hcov_x hcov_y
    exact ⟨by simp only [coverageSymmDiff]; rw [hcov_x, hcov_y], hcov_x⟩

/-- Max version of enlarged_symmDiff_eq_min for QPROT (scans from top).
    The proof shows a₀ > a₁ is impossible: going above a₀ to the next S-value u,
    coverageSet_stable gives H_{a₀} = H_u, but u > max(DT_S) means H_u(x) = H_u(y),
    contradicting a₀ ∈ DT_T. -/
theorem enlarged_symmDiff_eq_max {n : ℕ} (x y : Vec n)
    (S T : Finset ℝ) (hST : S ⊆ T)
    (hx : ∀ i : Fin n, x i ∈ S) (hy : ∀ i : Fin n, y i ∈ S)
    (hS_ne : (S.filter (fun a => coverageSet x a ≠ coverageSet y a)).Nonempty)
    (hT_ne : (T.filter (fun a => coverageSet x a ≠ coverageSet y a)).Nonempty) :
    coverageSymmDiff x y ((T.filter (fun a => coverageSet x a ≠ coverageSet y a)).max' hT_ne) =
    coverageSymmDiff x y ((S.filter (fun a => coverageSet x a ≠ coverageSet y a)).max' hS_ne) ∧
    coverageSet x ((T.filter (fun a => coverageSet x a ≠ coverageSet y a)).max' hT_ne) =
    coverageSet x ((S.filter (fun a => coverageSet x a ≠ coverageSet y a)).max' hS_ne) := by
  set DT_S := S.filter (fun a => coverageSet x a ≠ coverageSet y a) with hDT_S_def
  set DT_T := T.filter (fun a => coverageSet x a ≠ coverageSet y a) with hDT_T_def
  set a₁ := DT_S.max' hS_ne
  set a₀ := DT_T.max' hT_ne
  have hDT_sub : DT_S ⊆ DT_T := fun t ht =>
    Finset.mem_filter.mpr ⟨hST (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2⟩
  have ha₁_le : a₁ ≤ a₀ := Finset.le_max' _ a₁ (hDT_sub (Finset.max'_mem _ hS_ne))
  -- Show a₁ = a₀ (the strict inequality case is impossible)
  have ha_eq : a₁ = a₀ := by
    rcases eq_or_lt_of_le ha₁_le with h | ha₁_lt
    · exact h
    · exfalso
      -- a₀ ∉ S (otherwise a₀ ∈ DT_S, contradicting a₀ > a₁ = max(DT_S))
      have ha₀_not_S : a₀ ∉ S := by
        intro h
        exact absurd (Finset.le_max' DT_S a₀ (Finset.mem_filter.mpr
          ⟨h, (Finset.mem_filter.mp (Finset.max'_mem _ hT_ne)).2⟩)) (not_le.mpr ha₁_lt)
      have hx_ne : ∀ i, x i ≠ a₀ := fun i h => ha₀_not_S (h ▸ hx i)
      have hy_ne : ∀ i, y i ≠ a₀ := fun i h => ha₀_not_S (h ▸ hy i)
      -- There must be an S-value above a₀ (otherwise all coords < a₀, coverage empty)
      have hS_above_ne : (S.filter (fun t => a₀ < t)).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        -- All S-values ≤ a₀. Since a₀ ∉ S, all S-values < a₀. So all coords < a₀.
        have hcoord_lt : ∀ i, x i < a₀ ∧ y i < a₀ := by
          intro i
          refine ⟨?_, ?_⟩ <;> {
            rcases lt_or_ge _ a₀ with hlt | hge
            · exact hlt
            · rcases eq_or_lt_of_le hge with heq | hgt
              · exfalso; first | exact hx_ne i heq.symm | exact hy_ne i heq.symm
              · exfalso
                have hmem : _ ∈ S.filter (fun t => a₀ < t) :=
                  Finset.mem_filter.mpr ⟨by first | exact hx i | exact hy i, hgt⟩
                rw [hempty] at hmem; exact absurd hmem (by simp) }
        have hx_empty : coverageSet x a₀ = ∅ := by
          simp only [coverageSet]
          rw [Finset.filter_eq_empty_iff]
          intro i _; exact not_le.mpr (hcoord_lt i).1
        have hy_empty : coverageSet y a₀ = ∅ := by
          simp only [coverageSet]
          rw [Finset.filter_eq_empty_iff]
          intro i _; exact not_le.mpr (hcoord_lt i).2
        exact (Finset.mem_filter.mp (Finset.max'_mem _ hT_ne)).2 (by rw [hx_empty, hy_empty])
      -- Let u = min S-value above a₀
      set u := (S.filter (fun t => a₀ < t)).min' hS_above_ne
      have hu_gt : a₀ < u := (Finset.mem_filter.mp (Finset.min'_mem _ hS_above_ne)).2
      have hu_S : u ∈ S := (Finset.mem_filter.mp (Finset.min'_mem _ hS_above_ne)).1
      -- coverageSet_stable: H_{a₀}(x) = H_u(x) (no coord values in [a₀, u))
      have hcov_x : coverageSet x a₀ = coverageSet x u := by
        apply coverageSet_stable _ _ _ (le_of_lt hu_gt)
        intro i; rcases lt_or_ge (x i) a₀ with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.min'_le _ (x i) (Finset.mem_filter.mpr
            ⟨hx i, lt_of_le_of_ne h (Ne.symm (hx_ne i))⟩))
      have hcov_y : coverageSet y a₀ = coverageSet y u := by
        apply coverageSet_stable _ _ _ (le_of_lt hu_gt)
        intro i; rcases lt_or_ge (y i) a₀ with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.min'_le _ (y i) (Finset.mem_filter.mpr
            ⟨hy i, lt_of_le_of_ne h (Ne.symm (hy_ne i))⟩))
      -- u > a₁ = max(DT_S), so u ∉ DT_S, so coverage agrees at u
      have hu_agree : coverageSet x u = coverageSet y u := by
        by_contra hne_u
        exact absurd (Finset.le_max' _ u (Finset.mem_filter.mpr ⟨hu_S, hne_u⟩))
          (not_le.mpr (lt_trans ha₁_lt hu_gt))
      -- But H_{a₀}(x) = H_u(x) = H_u(y) = H_{a₀}(y), contradicting a₀ ∈ DT_T
      exact (Finset.mem_filter.mp (Finset.max'_mem _ hT_ne)).2
        (by rw [hcov_x, hcov_y, hu_agree])
  rw [show a₀ = a₁ from ha_eq.symm]; exact ⟨rfl, rfl⟩

/-- The successor of a Fin value, when it exists. -/
def Fin.succFin {n : ℕ} (j : Fin n) (h : j.val + 1 < n) : Fin n :=
  ⟨j.val + 1, h⟩

theorem Fin.succFin_val {n : ℕ} (j : Fin n) (h : j.val + 1 < n) :
    (Fin.succFin j h).val = j.val + 1 := rfl

/-! ## Symmetry lemmas for threshold/coverage definitions -/

theorem thresholdValues_comm {n : ℕ} (x y : Vec n) :
    thresholdValues x y = thresholdValues y x := by
  simp [thresholdValues, Finset.union_comm]

theorem differingThresholds_comm {n : ℕ} (x y : Vec n) :
    differingThresholds x y = differingThresholds y x := by
  unfold differingThresholds
  rw [thresholdValues_comm]
  ext a; simp only [Finset.mem_filter]
  exact and_congr_right' ne_comm

theorem coverageSymmDiff_comm {n : ℕ} (x y : Vec n) (a : ℝ) :
    coverageSymmDiff x y a = coverageSymmDiff y x a := by
  simp [coverageSymmDiff, symmDiff_comm]
