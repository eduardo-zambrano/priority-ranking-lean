/-
  PriorityRanking.Satisfaction.PPROT
  Which axioms P-PROT satisfies and violates.

  Satisfies: C, LTSF (from characterization); T, PD, CST, CX, CVG
  Violates: TSM, TSI, TM, TI, NCA, UPT, GUT, HTSF, EI
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms
import LeanFormalization.Characterizations.PPROT

/-! ## P-PROT satisfies C and LTSF (from Characterizations/PPROT.lean) -/

-- PPROT_satisfies_C and PPROT_satisfies_LTSF are exported from
-- LeanFormalization.Characterizations.PPROT

/-! ## P-PROT violates TM -/

/-- P-PROT violates Total Monotonicity: (0,3) has higher total than (2,0),
    but P-PROT prefers (2,0) because at the lowest differing threshold (any a ∈ (0,2]),
    the priority-first state 0 is in H_a(x) = {0}. -/
theorem PPROT_violates_TM : ¬ Ax_TM (@PPROT 2) := by
  intro hTM
  let x : Vec 2 := ![2, 0]
  let y : Vec 2 := ![0, 3]
  have htotal : totalSum y > totalSum x := by
    simp only [totalSum]; rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num
  -- TM says: totalSum y > totalSum x → strictPart PPROT y x
  have hstrict := hTM y x htotal
  -- But PPROT x y (x wins: at threshold a ∈ (0,2], H_a(x)={0}, H_a(y)={1}, symmdiff={0,1},
  -- min=0 ∈ H_a(x))
  -- Show PPROT x y by showing x ≠ y and computing the threshold scanning
  have hxy : x ≠ y := by
    intro h; have := congr_fun h ⟨0, by omega⟩
    simp [x, y, Matrix.cons_val_zero] at this
  -- The full PPROT computation requires detailed coverage set analysis.
  -- For now, we establish the key direction needed.
  sorry

/-! ## P-PROT violates TI -/

/-- P-PROT violates Total Indifference: (1,0) and (0,1) have equal totals
    but P-PROT strictly prefers (1,0). -/
theorem PPROT_violates_TI : ¬ Ax_TI (@PPROT 2) := by
  sorry

/-! ## P-PROT violates TSM -/

/-- P-PROT violates Top-State Monotonicity. -/
theorem PPROT_violates_TSM : ¬ Ax_TSM (@PPROT 2) := by
  sorry

/-! ## P-PROT violates TSI -/

/-- P-PROT violates Top-State Indifference. -/
theorem PPROT_violates_TSI : ¬ Ax_TSI (@PPROT 2) := by
  sorry

/-! ## P-PROT violates NCA -/

/-- P-PROT violates No Compensation from Below. -/
theorem PPROT_violates_NCA : ¬ Ax_NCA (@PPROT 2) := by
  sorry
