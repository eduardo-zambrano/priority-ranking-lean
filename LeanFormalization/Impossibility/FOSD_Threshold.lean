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

set_option linter.unusedSimpArgs false in
/-! ## Helper: compute prefix sums for Fin 2 vectors -/

private theorem fosdStrict_of_values {x y : Vec 2}
    (h0 : x ⟨0, by omega⟩ ≥ y ⟨0, by omega⟩)
    (h1 : x ⟨0, by omega⟩ + x ⟨1, by omega⟩ ≥ y ⟨0, by omega⟩ + y ⟨1, by omega⟩)
    (hs : x ⟨0, by omega⟩ > y ⟨0, by omega⟩) :
    fosdStrict x y := by
  refine ⟨fun j => ?_, ⟨⟨0, by omega⟩, ?_⟩⟩
  · fin_cases j
    · rw [prefixSum_zero x (by omega), prefixSum_zero y (by omega)]; exact h0
    · rw [prefixSum_succ x 0 (by omega) (by omega), prefixSum_zero x (by omega),
          prefixSum_succ y 0 (by omega) (by omega), prefixSum_zero y (by omega)]; exact h1
  · rw [prefixSum_zero x (by omega), prefixSum_zero y (by omega)]; exact hs

set_option linter.unusedSimpArgs false

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
  -- 1 ∈ differingThresholds x y
  have h1_dt : (1 : ℝ) ∈ differingThresholds x y := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inr ⟨⟨0, by omega⟩, by simp [y, Matrix.cons_val_zero]⟩
    · intro heq
      have h1 : (⟨1, by omega⟩ : Fin 2) ∈ coverageSet y 1 := by
        rw [mem_coverageSet]; show (1 : ℝ) ≤ y ⟨1, by omega⟩
        simp [y, Matrix.cons_val_one, Matrix.head_cons]
      rw [← heq, mem_coverageSet] at h1
      have : x (⟨1, by omega⟩ : Fin 2) = (0 : ℝ) := by
        simp [x, Matrix.cons_val_one, Matrix.head_cons]
      linarith
  -- min(differingThresholds) = 1
  have hmin_eq : (differingThresholds x y).min' hne = 1 := by
    apply le_antisymm (Finset.min'_le _ _ h1_dt)
    apply Finset.le_min'; intro b hb
    rw [differingThresholds, Finset.mem_filter] at hb
    obtain ⟨hb_tv, hb_diff⟩ := hb
    simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
    rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i
    · -- b = x₀ = 3: 1 ≤ 3
      simp [x, Matrix.cons_val_zero]
    · -- b = x₁ = 0: coverage sets equal at 0, contradiction
      exfalso; apply hb_diff; ext ⟨j, hj⟩; simp only [mem_coverageSet]
      interval_cases j <;> simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · -- b = y₀ = 1: 1 ≤ 1
      simp [y, Matrix.cons_val_zero]
    · -- b = y₁ = 1: 1 ≤ 1
      simp [y, Matrix.cons_val_one, Matrix.head_cons]
  -- Transport to threshold 1
  have hcsd_eq := congr_arg (coverageSymmDiff x y) hmin_eq
  have hcs_eq := congr_arg (coverageSet x) hmin_eq
  have hD' : (coverageSymmDiff x y 1).Nonempty := hcsd_eq ▸ hD
  -- Symmetric difference at 1 = {⟨1,_⟩}
  have h_csd_val : coverageSymmDiff x y 1 = {(⟨1, by omega⟩ : Fin 2)} := by
    ext ⟨j, hj⟩; simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet, mem_singleton,
      Fin.ext_iff]
    interval_cases j <;> simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  -- min({⟨1,_⟩}) = ⟨1,_⟩
  have hmin_sd : (coverageSymmDiff x y 1).min' hD' = ⟨1, by omega⟩ := by
    rw [Finset.min'_of_eq h_csd_val hD' ⟨_, mem_singleton.mpr rfl⟩]
    exact Finset.min'_singleton _
  -- Derive contradiction
  have hmem := hltsf.mp hFOSDxy.1
  have hmem' : (coverageSymmDiff x y 1).min' hD' ∈ coverageSet x 1 := by
    rw [← hcs_eq, ← Finset.min'_of_eq hcsd_eq hD hD']; exact hmem
  rw [hmin_sd, mem_coverageSet] at hmem'
  have : x (⟨1, by omega⟩ : Fin 2) = (0 : ℝ) := by
    simp [x, Matrix.cons_val_one, Matrix.head_cons]
  linarith

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
  -- 3 ∈ differingThresholds x y
  have h3_dt : (3 : ℝ) ∈ differingThresholds x y := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inr ⟨⟨1, by omega⟩, by simp [y, Matrix.cons_val_one, Matrix.head_cons]⟩
    · intro heq
      have h1 : (⟨1, by omega⟩ : Fin 2) ∈ coverageSet y 3 := by
        rw [mem_coverageSet]; show (3 : ℝ) ≤ y ⟨1, by omega⟩
        simp [y, Matrix.cons_val_one, Matrix.head_cons]
      rw [← heq, mem_coverageSet] at h1
      have : x (⟨1, by omega⟩ : Fin 2) = (2 : ℝ) := by
        simp [x, Matrix.cons_val_one, Matrix.head_cons]
      linarith
  -- max(differingThresholds) = 3
  have hmax_eq : (differingThresholds x y).max' hne = 3 := by
    apply le_antisymm
    · apply Finset.max'_le; intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb
      obtain ⟨hb_tv, _⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i <;>
        simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> norm_num
    · exact Finset.le_max' _ _ h3_dt
  -- Transport to threshold 3
  have hcsd_eq := congr_arg (coverageSymmDiff x y) hmax_eq
  have hcs_eq := congr_arg (coverageSet x) hmax_eq
  have hD' : (coverageSymmDiff x y 3).Nonempty := hcsd_eq ▸ hD
  -- Symmetric difference at 3 = {⟨1,_⟩}
  have h_csd_val : coverageSymmDiff x y 3 = {(⟨1, by omega⟩ : Fin 2)} := by
    ext ⟨j, hj⟩; simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet, mem_singleton,
      Fin.ext_iff]
    interval_cases j <;>
      simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> norm_num
  -- min({⟨1,_⟩}) = ⟨1,_⟩
  have hmin_sd : (coverageSymmDiff x y 3).min' hD' = ⟨1, by omega⟩ := by
    rw [Finset.min'_of_eq h_csd_val hD' ⟨_, mem_singleton.mpr rfl⟩]
    exact Finset.min'_singleton _
  -- Derive contradiction
  have hmem := hhtsf.mp hFOSDxy.1
  have hmem' : (coverageSymmDiff x y 3).min' hD' ∈ coverageSet x 3 := by
    rw [← hcs_eq, ← Finset.min'_of_eq hcsd_eq hD hD']; exact hmem
  rw [hmin_sd, mem_coverageSet] at hmem'
  have : x (⟨1, by omega⟩ : Fin 2) = (2 : ℝ) := by
    simp [x, Matrix.cons_val_one, Matrix.head_cons]
  linarith
