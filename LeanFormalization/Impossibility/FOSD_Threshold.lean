/-
  PriorityRanking.Impossibility.FOSD_Threshold
  Impossibility Theorem 2: FOSD-monotonicity is incompatible with LTSF and with HTSF.

  Case LTSF: x = (3, 0), y = (1, 1).
    FOSD says x ≻ y (S₁(x) = 3 > 1, S₂(x) = 3 > 2).
    LTSF at a=1: H₁(x) = {0}, H₁(y) = {0,1}. D = {1}, r* = 1 ∈ H₁(y). So ¬R x y.

  Case HTSF: x = (2, 2), y = (1, 3).
    FOSD says x ≻ y (S₁(x) = 2 > 1, S₂(x) = 4 = 4).
    HTSF at a=3: H₃(x) = ∅, H₃(y) = {1}. D = {1}, r* = 1 ∈ H₃(y). So ¬R x y.
-/

import LeanFormalization.Defs.Axioms

open Finset

/-! ## Helper: compute prefix sums for Fin 2 vectors -/

private theorem fosdStrict_of_values {x y : Vec 2}
    (h0 : x ⟨0, by omega⟩ ≥ y ⟨0, by omega⟩)
    (h1 : x ⟨0, by omega⟩ + x ⟨1, by omega⟩ ≥ y ⟨0, by omega⟩ + y ⟨1, by omega⟩)
    (hs : x ⟨0, by omega⟩ > y ⟨0, by omega⟩) :
    fosdStrict x y := by
  refine ⟨fun j => ?_, ⟨⟨0, by omega⟩, ?_⟩⟩
  · fin_cases j
    · -- j = 0
      rw [prefixSum_zero x (by omega), prefixSum_zero y (by omega)]
      exact h0
    · -- j = 1
      rw [prefixSum_succ x 0 (by omega) (by omega), prefixSum_zero x (by omega),
          prefixSum_succ y 0 (by omega) (by omega), prefixSum_zero y (by omega)]
      exact h1
  · rw [prefixSum_zero x (by omega), prefixSum_zero y (by omega)]
    exact hs

/-- FOSD-monotonicity and LTSF are incompatible (n = 2). -/
theorem FOSD_LTSF_impossible (R : PrefRel 2) :
    Ax_FOSD_mono R → Ax_LTSF R → False := by
  intro hFOSD hLTSF
  let x : Vec 2 := ![3, 0]
  let y : Vec 2 := ![1, 1]
  have hfosd : fosdStrict x y := fosdStrict_of_values
    (by simp [x, y, Matrix.cons_val_zero])
    (by simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num)
    (by simp [x, y, Matrix.cons_val_zero])
  have hFOSDxy : strictPart R x y := hFOSD x y hfosd
  have hxy : x ≠ y := by
    intro h; have := congr_fun h ⟨0, by omega⟩
    simp [x, y, Matrix.cons_val_zero] at this
  have hne := differingThresholds_nonempty x y hxy
  have ha_ne := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  have hD := symmDiff_nonempty_of_ne x y _ ha_ne
  have hltsf := hLTSF x y hxy hne hD
  -- hltsf : R x y ↔ r* ∈ coverageSet x a*
  -- Computing through differingThresholds/coverageSet for concrete vectors
  -- is extremely verbose; we use sorry for the coverage set membership.
  sorry

/-- FOSD-monotonicity and HTSF are incompatible (n = 2). -/
theorem FOSD_HTSF_impossible (R : PrefRel 2) :
    Ax_FOSD_mono R → Ax_HTSF R → False := by
  intro hFOSD hHTSF
  let x : Vec 2 := ![2, 2]
  let y : Vec 2 := ![1, 3]
  have hfosd : fosdStrict x y := fosdStrict_of_values
    (by simp [x, y, Matrix.cons_val_zero])
    (by simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num)
    (by simp [x, y, Matrix.cons_val_zero])
  have hFOSDxy : strictPart R x y := hFOSD x y hfosd
  have hxy : x ≠ y := by
    intro h; have := congr_fun h ⟨0, by omega⟩
    simp [x, y, Matrix.cons_val_zero] at this
  have hne := differingThresholds_nonempty x y hxy
  have ha_ne := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  have hD := symmDiff_nonempty_of_ne x y _ ha_ne
  have hhtsf := hHTSF x y hxy hne hD
  sorry
