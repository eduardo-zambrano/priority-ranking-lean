/-
  PriorityRanking.Characterizations.TMM
  Theorem 3: TMM is characterized by TM + TI.

  A preference ≿ on X is TMM if and only if it satisfies TM and TI.
  Moreover, C and T are redundant (implied by TM + TI).
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms

/-! ## Forward direction: TMM satisfies TM and TI -/

theorem TMM_satisfies_TM {n : ℕ} : Ax_TM (@TMM n) := by
  intro x y hgt
  rw [TMM_strict]
  exact hgt

theorem TMM_satisfies_TI {n : ℕ} : Ax_TI (@TMM n) := by
  intro x y heq
  simp only [indiffPart, TMM, ge_iff_le]
  exact ⟨le_of_eq heq.symm, le_of_eq heq⟩

/-! ## Reverse direction: TM + TI implies TMM -/

/-- Any preference satisfying TM + TI agrees with TMM on all pairs. -/
theorem TM_TI_imp_TMM {n : ℕ} (R : PrefRel n)
    (hTM : Ax_TM R) (hTI : Ax_TI R) :
    ∀ x y, R x y ↔ TMM x y := by
  intro x y
  constructor
  · -- R x y → TMM x y (i.e., totalSum x ≥ totalSum y)
    intro hRxy
    simp only [TMM, ge_iff_le]
    by_contra h
    push_neg at h
    -- h : totalSum x < totalSum y, so TM gives y ≻ x
    have hyx := hTM y x h
    exact hyx.2 hRxy
  · -- TMM x y → R x y
    intro hTMM
    simp only [TMM, ge_iff_le] at hTMM
    rcases eq_or_lt_of_le hTMM with heq | hlt
    · exact (hTI x y heq.symm).1
    · exact (hTM x y hlt).1

/-! ## Characterization theorem -/

/-- **Theorem 3**: A preference is TMM iff it satisfies TM and TI. -/
theorem TMM_characterization {n : ℕ} (R : PrefRel n) :
    (∀ x y, R x y ↔ TMM x y) ↔ (Ax_TM R ∧ Ax_TI R) := by
  constructor
  · intro hR
    exact ⟨
      fun x y hgt => by
        rw [strictPart]; constructor
        · exact (hR x y).mpr (TMM_satisfies_TM x y hgt).1
        · intro hyx; exact (TMM_satisfies_TM x y hgt).2 ((hR y x).mp hyx),
      fun x y heq => by
        rw [indiffPart]; exact ⟨
          (hR x y).mpr (TMM_satisfies_TI x y heq).1,
          (hR y x).mpr (TMM_satisfies_TI x y heq).2⟩⟩
  · intro ⟨hTM, hTI⟩
    exact TM_TI_imp_TMM R hTM hTI

/-! ## Redundancy: C and T are implied by TM + TI -/

theorem TM_TI_imp_C {n : ℕ} (R : PrefRel n)
    (hTM : Ax_TM R) (hTI : Ax_TI R) : Ax_C R := by
  intro x y
  rcases lt_trichotomy (totalSum x) (totalSum y) with h | h | h
  · exact Or.inr (hTM y x h).1
  · exact Or.inl (hTI x y h).1
  · exact Or.inl (hTM x y h).1

theorem TM_TI_imp_T {n : ℕ} (R : PrefRel n)
    (hTM : Ax_TM R) (hTI : Ax_TI R) : Ax_T R := by
  intro x y z hxy hyz
  have hxy' := (TM_TI_imp_TMM R hTM hTI x y).mp hxy
  have hyz' := (TM_TI_imp_TMM R hTM hTI y z).mp hyz
  exact (TM_TI_imp_TMM R hTM hTI x z).mpr (le_trans hyz' hxy')
