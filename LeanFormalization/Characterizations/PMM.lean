/-
  PriorityRanking.Characterizations.PMM
  Theorem 1: PMM is characterized by TSM + TSI.

  A preference ≿ on X is PMM if and only if it satisfies TSM and TSI.
  Moreover, C and T are redundant (implied by TSM + TSI).
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms

/-! ## Forward direction: PMM satisfies TSM and TSI -/

theorem PMM_satisfies_TSM {n : ℕ} [NeZero n] : Ax_TSM (@PMM n _) := by
  intro x y hgt
  rw [PMM_strict]
  exact hgt

theorem PMM_satisfies_TSI {n : ℕ} [NeZero n] : Ax_TSI (@PMM n _) := by
  intro x y heq
  rw [PMM_indiff]
  exact heq

/-! ## Reverse direction: TSM + TSI implies PMM -/

/-- Any preference satisfying TSM + TSI agrees with PMM on all pairs. -/
theorem TSM_TSI_imp_PMM {n : ℕ} [NeZero n] (R : PrefRel n)
    (hTSM : Ax_TSM R) (hTSI : Ax_TSI R) :
    ∀ x y, R x y ↔ PMM x y := by
  intro x y
  constructor
  · -- R x y → PMM x y (i.e., x₀ ≥ y₀)
    intro hRxy
    simp only [PMM, ge_iff_le]
    by_contra h
    push_neg at h
    -- h : x₀ < y₀, so TSM gives y ≻ x, i.e., R y x ∧ ¬R x y
    have hyx := hTSM y x h
    exact hyx.2 hRxy
  · -- PMM x y → R x y (i.e., x₀ ≥ y₀ → R x y)
    intro hPMM
    simp only [PMM, ge_iff_le] at hPMM
    rcases eq_or_lt_of_le hPMM with heq | hlt
    · -- x₀ = y₀: TSI gives indifference
      exact (hTSI x y heq.symm).1
    · -- x₀ > y₀: TSM gives strict preference
      exact (hTSM x y hlt).1

/-! ## Characterization theorem -/

/-- **Theorem 1**: A preference is PMM iff it satisfies TSM and TSI. -/
theorem PMM_characterization {n : ℕ} [NeZero n] (R : PrefRel n) :
    (∀ x y, R x y ↔ PMM x y) ↔ (Ax_TSM R ∧ Ax_TSI R) := by
  constructor
  · -- If R = PMM, then R satisfies TSM and TSI
    intro hR
    exact ⟨
      fun x y hgt => by
        rw [strictPart]; constructor
        · exact (hR x y).mpr (PMM_satisfies_TSM x y hgt).1
        · intro hyx; exact (PMM_satisfies_TSM x y hgt).2 ((hR y x).mp hyx),
      fun x y heq => by
        rw [indiffPart]; exact ⟨
          (hR x y).mpr (PMM_satisfies_TSI x y heq).1,
          (hR y x).mpr (PMM_satisfies_TSI x y heq).2⟩⟩
  · -- If R satisfies TSM and TSI, then R = PMM
    intro ⟨hTSM, hTSI⟩
    exact TSM_TSI_imp_PMM R hTSM hTSI

/-! ## Redundancy: C and T are implied by TSM + TSI -/

theorem TSM_TSI_imp_C {n : ℕ} [NeZero n] (R : PrefRel n)
    (hTSM : Ax_TSM R) (hTSI : Ax_TSI R) : Ax_C R := by
  intro x y
  rcases lt_trichotomy (x ⟨0, NeZero.pos n⟩) (y ⟨0, NeZero.pos n⟩) with h | h | h
  · exact Or.inr (hTSM y x h).1
  · exact Or.inl (hTSI x y h).1
  · exact Or.inl (hTSM x y h).1

theorem TSM_TSI_imp_T {n : ℕ} [NeZero n] (R : PrefRel n)
    (hTSM : Ax_TSM R) (hTSI : Ax_TSI R) : Ax_T R := by
  intro x y z hxy hyz
  have hxy' := (TSM_TSI_imp_PMM R hTSM hTSI x y).mp hxy
  have hyz' := (TSM_TSI_imp_PMM R hTSM hTSI y z).mp hyz
  exact (TSM_TSI_imp_PMM R hTSM hTSI x z).mpr (le_trans hyz' hxy')
