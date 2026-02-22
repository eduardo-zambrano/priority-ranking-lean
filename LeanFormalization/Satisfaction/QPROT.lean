/-
  PriorityRanking.Satisfaction.QPROT
  Which axioms Q-PROT satisfies and violates.

  Satisfies: C, HTSF (from characterization); T, PD, CST, CX, CVG
  Violates: TSM, TSI, TM, TI, NCA, UPT, GUT, LTSF, EI
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms
import LeanFormalization.Characterizations.QPROT

/-! ## Q-PROT satisfies C and HTSF (from Characterizations/QPROT.lean) -/

-- QPROT_satisfies_C and QPROT_satisfies_HTSF are exported from
-- LeanFormalization.Characterizations.QPROT

/-! ## Q-PROT violates TM -/

/-- Q-PROT violates Total Monotonicity. -/
theorem QPROT_violates_TM : ¬ Ax_TM (@QPROT 2) := by
  sorry

/-! ## Q-PROT violates TI -/

/-- Q-PROT violates Total Indifference. -/
theorem QPROT_violates_TI : ¬ Ax_TI (@QPROT 2) := by
  sorry

/-! ## Q-PROT violates TSM -/

/-- Q-PROT violates Top-State Monotonicity. -/
theorem QPROT_violates_TSM : ¬ Ax_TSM (@QPROT 2) := by
  sorry

/-! ## Q-PROT violates TSI -/

/-- Q-PROT violates Top-State Indifference. -/
theorem QPROT_violates_TSI : ¬ Ax_TSI (@QPROT 2) := by
  sorry

/-! ## Q-PROT violates NCA -/

/-- Q-PROT violates No Compensation from Below. -/
theorem QPROT_violates_NCA : ¬ Ax_NCA (@QPROT 2) := by
  sorry
