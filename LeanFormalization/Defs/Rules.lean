/-
  PriorityRanking.Defs.Rules
  Definitions of the six priority-based ranking rules:
  PMM, PLS, TMM, TLS, P-PROT, Q-PROT.

  Paper reference: Section 2.3 (Definitions 4-9)
-/

import LeanFormalization.Basic
import Mathlib.Order.PiLex

open Finset

/-! ## PMM: Priority Maximin (Definition 4) -/

/-- PMM weak preference: x ≿_PMM y iff x₀ ≥ y₀.
    (Paper: x₁ ≥ y₁ in 1-based indexing.) -/
noncomputable def PMM {n : ℕ} [NeZero n] : PrefRel n :=
  fun x y => x ⟨0, NeZero.pos n⟩ ≥ y ⟨0, NeZero.pos n⟩

/-- PMM strict: x ≻_PMM y iff x₀ > y₀. -/
theorem PMM_strict {n : ℕ} [NeZero n] (x y : Vec n) :
    strictPart PMM x y ↔ x ⟨0, NeZero.pos n⟩ > y ⟨0, NeZero.pos n⟩ := by
  simp only [strictPart, PMM, ge_iff_le, not_le, gt_iff_lt]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; constructor <;> linarith

/-- PMM indifference: x ~_PMM y iff x₀ = y₀. -/
theorem PMM_indiff {n : ℕ} [NeZero n] (x y : Vec n) :
    indiffPart PMM x y ↔ x ⟨0, NeZero.pos n⟩ = y ⟨0, NeZero.pos n⟩ := by
  simp only [indiffPart, PMM, ge_iff_le]
  constructor
  · intro ⟨h1, h2⟩; exact le_antisymm h2 h1
  · intro h; exact ⟨le_of_eq h.symm, le_of_eq h⟩

/-! ## PLS: Priority Lexicographic by States (Definition 5) -/

/-- PLS strict preference: x ≻_PLS y iff at the first coordinate where x and y differ,
    x has the larger value.
    Uses Pi.Lex from Mathlib: Pi.Lex r s a b means ∃ i, (∀ j, r j i → a j = b j) ∧ s i (a i) (b i).
    With r = (· < ·) and s _ = (· < ·), Pi.Lex (· < ·) (· < ·) y x means
    "∃ i, (∀ j < i, y j = x j) ∧ y i < x i", i.e., x is PLS-strictly better than y. -/
noncomputable def PLS_strict {n : ℕ} (x y : Vec n) : Prop :=
  Pi.Lex (· < ·) (· < ·) y x

/-- PLS weak preference: x ≿_PLS y iff x = y or x ≻_PLS y. -/
noncomputable def PLS {n : ℕ} : PrefRel n :=
  fun x y => x = y ∨ PLS_strict x y

/-! ## TMM: Total Mass Maximin (Definition 6) -/

/-- TMM weak preference: x ≿_TMM y iff S_n(x) ≥ S_n(y). -/
noncomputable def TMM {n : ℕ} : PrefRel n :=
  fun x y => totalSum x ≥ totalSum y

/-- TMM strict: x ≻_TMM y iff S_n(x) > S_n(y). -/
theorem TMM_strict {n : ℕ} (x y : Vec n) :
    strictPart TMM x y ↔ totalSum x > totalSum y := by
  simp only [strictPart, TMM, ge_iff_le, not_le, gt_iff_lt]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; constructor <;> linarith

/-! ## TLS: Total-First Lexicographic (Definition 7) -/

/-- TLS strict preference: x ≻_TLS y iff at the last prefix-sum index where S_j(x) ≠ S_j(y),
    S_j(x) > S_j(y).

    This is lexicographic comparison of prefix sums scanning from bottom (largest index first).
    Using Pi.Lex with reversed index order: Pi.Lex (· > ·) (· < ·) on prefix vectors,
    applied as (prefixVec y, prefixVec x).

    Pi.Lex (· > ·) (· < ·) (prefixVec y) (prefixVec x) means:
    ∃ k, (∀ j, j > k → prefixVec y j = prefixVec x j) ∧ prefixVec y k < prefixVec x k
    i.e., ∃ k, (∀ j > k, S_j(x) = S_j(y)) ∧ S_k(x) > S_k(y). -/
noncomputable def TLS_strict {n : ℕ} (x y : Vec n) : Prop :=
  Pi.Lex (· > ·) (· < ·) (prefixVec y) (prefixVec x)

/-- TLS weak preference. -/
noncomputable def TLS {n : ℕ} : PrefRel n :=
  fun x y => x = y ∨ TLS_strict x y

/-! ## P-PROT: Priority-Protective (Definition 8) -/

/-- P-PROT strict preference.
    For x ≠ y: find a* = min threshold in thresholdValues(x,y) where coverage sets differ.
    Let D = symmetric difference of H_{a*}(x) and H_{a*}(y).
    Let r* = min element of D. Then x ≻ y iff r* ∈ H_{a*}(x). -/
noncomputable def PPROT_strict {n : ℕ} (x y : Vec n) : Prop :=
  ∃ (hne : (differingThresholds x y).Nonempty),
    ∃ (hD : (coverageSymmDiff x y ((differingThresholds x y).min' hne)).Nonempty),
      (coverageSymmDiff x y ((differingThresholds x y).min' hne)).min' hD ∈
        coverageSet x ((differingThresholds x y).min' hne)

/-- P-PROT weak preference. -/
noncomputable def PPROT {n : ℕ} : PrefRel n :=
  fun x y => x = y ∨ PPROT_strict x y

/-! ## Q-PROT: Quality-Protective (Definition 9) -/

/-- Q-PROT strict preference.
    Same as P-PROT but uses max threshold instead of min. -/
noncomputable def QPROT_strict {n : ℕ} (x y : Vec n) : Prop :=
  ∃ (hne : (differingThresholds x y).Nonempty),
    ∃ (hD : (coverageSymmDiff x y ((differingThresholds x y).max' hne)).Nonempty),
      (coverageSymmDiff x y ((differingThresholds x y).max' hne)).min' hD ∈
        coverageSet x ((differingThresholds x y).max' hne)

/-- Q-PROT weak preference. -/
noncomputable def QPROT {n : ℕ} : PrefRel n :=
  fun x y => x = y ∨ QPROT_strict x y

/-! ## Construction helpers for PPROT_strict / QPROT_strict -/

/-- Construct PPROT_strict from concrete threshold data. -/
theorem pprot_strict_of_data {n : ℕ} {x y : Vec n}
    (a : ℝ)
    (ha_mem : a ∈ differingThresholds x y)
    (ha_min : ∀ b, b ∈ differingThresholds x y → a ≤ b)
    (r : Fin n)
    (hr_mem : r ∈ coverageSymmDiff x y a)
    (hr_min : ∀ s, s ∈ coverageSymmDiff x y a → r ≤ s)
    (hr_x : r ∈ coverageSet x a) :
    PPROT_strict x y := by
  have hne : (differingThresholds x y).Nonempty := ⟨a, ha_mem⟩
  have ha_eq : (differingThresholds x y).min' hne = a := by
    apply le_antisymm (Finset.min'_le _ _ ha_mem)
    apply Finset.le_min'; intro b hb; exact ha_min b hb
  have hcsd_eq : coverageSymmDiff x y ((differingThresholds x y).min' hne) =
      coverageSymmDiff x y a := by rw [ha_eq]
  have hD : (coverageSymmDiff x y ((differingThresholds x y).min' hne)).Nonempty :=
    hcsd_eq ▸ ⟨r, hr_mem⟩
  refine ⟨hne, hD, ?_⟩
  have step1 := Finset.min'_of_eq hcsd_eq hD ⟨r, hr_mem⟩
  have step2 : (coverageSymmDiff x y a).min' ⟨r, hr_mem⟩ = r := by
    apply le_antisymm (Finset.min'_le _ _ hr_mem)
    apply Finset.le_min'; intro s hs; exact hr_min s hs
  rw [step1, step2, ha_eq]; exact hr_x

/-- Construct QPROT_strict from concrete threshold data (max version). -/
theorem qprot_strict_of_data {n : ℕ} {x y : Vec n}
    (a : ℝ)
    (ha_mem : a ∈ differingThresholds x y)
    (ha_max : ∀ b, b ∈ differingThresholds x y → b ≤ a)
    (r : Fin n)
    (hr_mem : r ∈ coverageSymmDiff x y a)
    (hr_min : ∀ s, s ∈ coverageSymmDiff x y a → r ≤ s)
    (hr_x : r ∈ coverageSet x a) :
    QPROT_strict x y := by
  have hne : (differingThresholds x y).Nonempty := ⟨a, ha_mem⟩
  have ha_eq : (differingThresholds x y).max' hne = a := by
    apply le_antisymm
    · apply Finset.max'_le; intro b hb; exact ha_max b hb
    · exact Finset.le_max' _ _ ha_mem
  have hcsd_eq : coverageSymmDiff x y ((differingThresholds x y).max' hne) =
      coverageSymmDiff x y a := by rw [ha_eq]
  have hD : (coverageSymmDiff x y ((differingThresholds x y).max' hne)).Nonempty :=
    hcsd_eq ▸ ⟨r, hr_mem⟩
  refine ⟨hne, hD, ?_⟩
  have step1 := Finset.min'_of_eq hcsd_eq hD ⟨r, hr_mem⟩
  have step2 : (coverageSymmDiff x y a).min' ⟨r, hr_mem⟩ = r := by
    apply le_antisymm (Finset.min'_le _ _ hr_mem)
    apply Finset.le_min'; intro s hs; exact hr_min s hs
  rw [step1, step2, ha_eq]; exact hr_x

/-- PPROT_strict is asymmetric. -/
theorem PPROT_strict_asymm {n : ℕ} (x y : Vec n) :
    PPROT_strict x y → ¬ PPROT_strict y x := by
  intro ⟨hne_xy, hD_xy, hmem_xy⟩ ⟨hne_yx, hD_yx, hmem_yx⟩
  have hdt_eq := differingThresholds_comm x y
  have hmin_eq := Finset.min'_of_eq hdt_eq hne_xy hne_yx
  set a_xy := (differingThresholds x y).min' hne_xy
  set a_yx := (differingThresholds y x).min' hne_yx
  have hcsd_eq : coverageSymmDiff x y a_xy = coverageSymmDiff y x a_yx := by
    rw [hmin_eq, coverageSymmDiff_comm]
  have hmin_sd := Finset.min'_of_eq hcsd_eq hD_xy hD_yx
  have hr_sd := Finset.min'_mem _ hD_xy
  simp only [coverageSymmDiff, Finset.mem_symmDiff] at hr_sd
  have hr_y : (coverageSymmDiff x y a_xy).min' hD_xy ∈ coverageSet y a_xy := by
    rw [hmin_sd, hmin_eq]; exact hmem_yx
  rcases hr_sd with ⟨_, hnot⟩ | ⟨_, hnot⟩
  · exact hnot hr_y
  · exact hnot hmem_xy

/-- QPROT_strict is asymmetric. -/
theorem QPROT_strict_asymm {n : ℕ} (x y : Vec n) :
    QPROT_strict x y → ¬ QPROT_strict y x := by
  intro ⟨hne_xy, hD_xy, hmem_xy⟩ ⟨hne_yx, hD_yx, hmem_yx⟩
  have hdt_eq := differingThresholds_comm x y
  have hmax_eq := Finset.max'_of_eq hdt_eq hne_xy hne_yx
  set a_xy := (differingThresholds x y).max' hne_xy
  set a_yx := (differingThresholds y x).max' hne_yx
  have hcsd_eq : coverageSymmDiff x y a_xy = coverageSymmDiff y x a_yx := by
    rw [hmax_eq, coverageSymmDiff_comm]
  have hmin_sd := Finset.min'_of_eq hcsd_eq hD_xy hD_yx
  have hr_sd := Finset.min'_mem _ hD_xy
  simp only [coverageSymmDiff, Finset.mem_symmDiff] at hr_sd
  have hr_y : (coverageSymmDiff x y a_xy).min' hD_xy ∈ coverageSet y a_xy := by
    rw [hmin_sd, hmax_eq]; exact hmem_yx
  rcases hr_sd with ⟨_, hnot⟩ | ⟨_, hnot⟩
  · exact hnot hr_y
  · exact hnot hmem_xy

/-- If x ≠ y and PPROT_strict x y, then strictPart PPROT x y. -/
theorem PPROT_strictPart_of_strict {n : ℕ} {x y : Vec n}
    (hne : x ≠ y) (h : PPROT_strict x y) : strictPart PPROT x y := by
  refine ⟨Or.inr h, ?_⟩
  intro hyx
  rcases hyx with rfl | hyx
  · exact hne rfl
  · exact PPROT_strict_asymm x y h hyx

/-- If x ≠ y and QPROT_strict x y, then strictPart QPROT x y. -/
theorem QPROT_strictPart_of_strict {n : ℕ} {x y : Vec n}
    (hne : x ≠ y) (h : QPROT_strict x y) : strictPart QPROT x y := by
  refine ⟨Or.inr h, ?_⟩
  intro hyx
  rcases hyx with rfl | hyx
  · exact hne rfl
  · exact QPROT_strict_asymm x y h hyx

/-! ## Basic properties of the rules -/

/-- All six rules are reflexive. -/
theorem PMM_refl {n : ℕ} [NeZero n] (x : Vec n) : PMM x x := le_refl _
theorem PLS_refl {n : ℕ} (x : Vec n) : PLS x x := Or.inl rfl
theorem TMM_refl {n : ℕ} (x : Vec n) : TMM x x := le_refl _
theorem TLS_refl {n : ℕ} (x : Vec n) : TLS x x := Or.inl rfl
theorem PPROT_refl {n : ℕ} (x : Vec n) : PPROT x x := Or.inl rfl
theorem QPROT_refl {n : ℕ} (x : Vec n) : QPROT x x := Or.inl rfl
