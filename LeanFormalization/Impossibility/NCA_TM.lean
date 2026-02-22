/-
  PriorityRanking.Impossibility.NCA_TM
  Impossibility Theorem 1: For n ≥ 2, no preference satisfies both NCA and TM.

  Proof: With n = 2, take x = (0, 10), y = (1, 0).
  - TM requires x ≻ y (S₂(x) = 10 > 1 = S₂(y))
  - NCA forbids x ≻ y (y₀ = 1 > 0 = x₀)
-/

import LeanFormalization.Defs.Axioms

open Finset

/-- NCA and TM are incompatible (proved for n = 2). -/
theorem NCA_TM_impossible (R : PrefRel 2) :
    Ax_NCA R → Ax_TM R → False := by
  intro hNCA hTM
  let x : Vec 2 := ![0, 10]
  let y : Vec 2 := ![1, 0]
  -- Step 1: TM gives x ≻ y since totalSum x = 10 > 1 = totalSum y
  have hsum : totalSum x > totalSum y := by
    simp only [totalSum, x, y]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num
  have hTMxy : strictPart R x y := hTM x y hsum
  -- Step 2: NCA forbids x ≻ y
  have hvac : ∀ i : Fin 2, i < (0 : Fin 2) → y i = x i := by
    intro i hi; exact absurd hi (not_lt.mpr (Fin.zero_le i))
  have hgt : y (0 : Fin 2) > x (0 : Fin 2) := by
    simp [x, y, Matrix.cons_val_zero]
  exact (hNCA y x 0 hvac hgt x (fun _ _ => rfl)) hTMxy
