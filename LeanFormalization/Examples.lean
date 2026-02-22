/-
  PriorityRanking.Examples
  Concrete sanity checks validating the definitions against Example 3.5
  from the paper: x = (3, 1, 0), y = (2, 0, 3) with n = 3.

  Expected rankings:
  - PMM: x ≻ y  (x₀ = 3 > 2 = y₀)
  - PLS: x ≻ y  (first diff at 0: 3 > 2)
  - TMM: y ≻ x  (total y = 5 > 4 = total x)
  - TLS: y ≻ x  (k* = 2: S₂(y) = 5 > 4 = S₂(x))
  - P-PROT: x ≻ y  (at a=1: coverage sets differ, priority tiebreak favors x)
  - Q-PROT: x ≻ y  (at a=3: coverage sets differ, priority tiebreak favors x)
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms

/-! ## Test vectors for n = 3 -/

/-- x = (3, 1, 0) -/
noncomputable def test_x : Vec 3 := ![3, 1, 0]

/-- y = (2, 0, 3) -/
noncomputable def test_y : Vec 3 := ![2, 0, 3]

/-! ## PMM: x ≻ y (x₀ = 3 > 2 = y₀) -/

example : strictPart (@PMM 3 _) test_x test_y := by
  rw [PMM_strict]
  simp [test_x, test_y, Matrix.cons_val_zero]
  norm_num

/-! ## PLS: x ≻ y (first diff at index 0: 3 > 2) -/

example : PLS_strict test_x test_y := by
  simp only [PLS_strict, Pi.Lex]
  exact ⟨⟨0, by omega⟩, fun j hj => absurd hj (not_lt.mpr (Fin.zero_le j)),
    by simp [test_x, test_y, Matrix.cons_val_zero]; norm_num⟩

/-! ## Test: x and y are distinct -/

example : test_x ≠ test_y := by
  intro h
  have := congr_fun h ⟨0, by omega⟩
  simp [test_x, test_y, Matrix.cons_val_zero] at this
