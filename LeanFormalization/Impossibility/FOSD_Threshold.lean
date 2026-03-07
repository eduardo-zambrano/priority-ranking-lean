/-
  PriorityRanking.Impossibility.FOSD_Threshold
  Impossibility: FOSD-monotonicity is incompatible with NUTC and with NDTC.
  (Paper Theorem 4.2)

  Also proves the stronger intermediate result for LTSF and HTSF.

  Case NUTC (= Case LTSF): x = (3, 0), y = (1, 1).
    FOSD says x ≻ y (S₁(x) = 3 > 1, S₂(x) = 3 > 2).
    NUTC applied to (y, x): min differing threshold = 1, D = {1}, r* = 1 ∈ H₁(y).
    So ¬(x ≻ y), contradicting FOSD.

  Case NDTC (= Case HTSF): x = (2, 2), y = (1, 3).
    FOSD says x ≻ y (S₁(x) = 2 > 1, S₂(x) = 4 = 4).
    NDTC applied to (y, x): max differing threshold = 3, D = {1}, r* = 1 ∈ H₃(y).
    So ¬(x ≻ y), contradicting FOSD.
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

/-- FOSD-monotonicity and NUTC are incompatible (n = 2).
    Paper Theorem 4.2, Case 1. Same counterexample as LTSF, but applies
    NUTC to (y, x) using symmetry of differingThresholds and coverageSymmDiff. -/
theorem FOSD_NUTC_impossible (R : PrefRel 2) :
    Ax_FOSD_mono R → Ax_NUTC R → False := by
  intro hFOSD hNUTC
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
  have hyx : y ≠ x := Ne.symm hxy
  -- differingThresholds y x = differingThresholds x y
  have hdt_comm : differingThresholds y x = differingThresholds x y :=
    differingThresholds_comm y x
  have hne := differingThresholds_nonempty x y hxy
  have hne_yx : (differingThresholds y x).Nonempty := hdt_comm ▸ hne
  -- 1 ∈ differingThresholds x y (same computation as LTSF proof)
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
  -- min(differingThresholds x y) = 1
  have hmin_eq : (differingThresholds x y).min' hne = 1 := by
    apply le_antisymm (Finset.min'_le _ _ h1_dt)
    apply Finset.le_min'; intro b hb
    rw [differingThresholds, Finset.mem_filter] at hb
    obtain ⟨hb_tv, hb_diff⟩ := hb
    simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
    rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i
    · simp [x, Matrix.cons_val_zero]
    · exfalso; apply hb_diff; ext ⟨j, hj⟩; simp only [mem_coverageSet]
      interval_cases j <;> simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · simp [y, Matrix.cons_val_zero]
    · simp [y, Matrix.cons_val_one, Matrix.head_cons]
  -- min(differingThresholds y x) = 1 (via comm)
  have hmin_yx : (differingThresholds y x).min' hne_yx = 1 := by
    rw [Finset.min'_of_eq hdt_comm hne_yx hne]; exact hmin_eq
  -- Nonemptiness of symmetric difference
  have ha_ne := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  have hD := symmDiff_nonempty_of_ne x y _ ha_ne
  -- coverageSymmDiff y x 1 = coverageSymmDiff x y 1
  have hcsd_comm := coverageSymmDiff_comm y x 1
  -- Transport nonemptiness through comm
  have hcsd_eq := congr_arg (coverageSymmDiff x y) hmin_eq
  have hD' : (coverageSymmDiff x y 1).Nonempty := hcsd_eq ▸ hD
  have hcsd_yx_eq := congr_arg (coverageSymmDiff y x) hmin_yx
  have hD_yx : (coverageSymmDiff y x ((differingThresholds y x).min' hne_yx)).Nonempty := by
    rw [hmin_yx, hcsd_comm]; exact hD'
  -- Symmetric difference at 1 = {⟨1,_⟩}
  have h_csd_val : coverageSymmDiff x y 1 = {(⟨1, by omega⟩ : Fin 2)} := by
    ext ⟨j, hj⟩; simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet, mem_singleton,
      Fin.ext_iff]
    interval_cases j <;> simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  -- min({⟨1,_⟩}) = ⟨1,_⟩ in coverageSymmDiff y x
  have hmin_sd : (coverageSymmDiff y x ((differingThresholds y x).min' hne_yx)).min' hD_yx =
      ⟨1, by omega⟩ := by
    have : coverageSymmDiff y x ((differingThresholds y x).min' hne_yx) =
        {(⟨1, by omega⟩ : Fin 2)} := by
      rw [hmin_yx, hcsd_comm, h_csd_val]
    rw [Finset.min'_of_eq this hD_yx ⟨_, mem_singleton.mpr rfl⟩]
    exact Finset.min'_singleton _
  -- r* = ⟨1,_⟩ ∈ H₁(y)
  have hmem_y : (coverageSymmDiff y x ((differingThresholds y x).min' hne_yx)).min' hD_yx ∈
      coverageSet y ((differingThresholds y x).min' hne_yx) := by
    rw [hmin_sd, hmin_yx, mem_coverageSet]
    change (1 : ℝ) ≤ y ⟨1, by omega⟩
    simp [y, Matrix.cons_val_one, Matrix.head_cons]
  -- NUTC(y, x) gives ¬ strictPart R x y
  exact (hNUTC y x hyx hne_yx hD_yx hmem_y) hFOSDxy

/-- FOSD-monotonicity and NDTC are incompatible (n = 2).
    Paper Theorem 4.2, Case 2. Same counterexample as HTSF, but applies
    NDTC to (y, x) using symmetry of differingThresholds and coverageSymmDiff. -/
theorem FOSD_NDTC_impossible (R : PrefRel 2) :
    Ax_FOSD_mono R → Ax_NDTC R → False := by
  intro hFOSD hNDTC
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
  have hyx : y ≠ x := Ne.symm hxy
  -- differingThresholds y x = differingThresholds x y
  have hdt_comm : differingThresholds y x = differingThresholds x y :=
    differingThresholds_comm y x
  have hne := differingThresholds_nonempty x y hxy
  have hne_yx : (differingThresholds y x).Nonempty := hdt_comm ▸ hne
  -- 3 ∈ differingThresholds x y (same computation as HTSF proof)
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
  -- max(differingThresholds x y) = 3
  have hmax_eq : (differingThresholds x y).max' hne = 3 := by
    apply le_antisymm
    · apply Finset.max'_le; intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb
      obtain ⟨hb_tv, _⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i <;>
        simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> norm_num
    · exact Finset.le_max' _ _ h3_dt
  -- max(differingThresholds y x) = 3 (via comm)
  have hmax_yx : (differingThresholds y x).max' hne_yx = 3 := by
    rw [Finset.max'_of_eq hdt_comm hne_yx hne]; exact hmax_eq
  -- Nonemptiness of symmetric difference
  have ha_ne := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  have hD := symmDiff_nonempty_of_ne x y _ ha_ne
  -- coverageSymmDiff y x 3 = coverageSymmDiff x y 3
  have hcsd_comm := coverageSymmDiff_comm y x 3
  -- Transport nonemptiness through comm
  have hcsd_eq := congr_arg (coverageSymmDiff x y) hmax_eq
  have hD' : (coverageSymmDiff x y 3).Nonempty := hcsd_eq ▸ hD
  have hcsd_yx_eq := congr_arg (coverageSymmDiff y x) hmax_yx
  have hD_yx : (coverageSymmDiff y x ((differingThresholds y x).max' hne_yx)).Nonempty := by
    rw [hmax_yx, hcsd_comm]; exact hD'
  -- Symmetric difference at 3 = {⟨1,_⟩}
  have h_csd_val : coverageSymmDiff x y 3 = {(⟨1, by omega⟩ : Fin 2)} := by
    ext ⟨j, hj⟩; simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet, mem_singleton,
      Fin.ext_iff]
    interval_cases j <;>
      simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> norm_num
  -- min({⟨1,_⟩}) = ⟨1,_⟩ in coverageSymmDiff y x
  have hmin_sd : (coverageSymmDiff y x ((differingThresholds y x).max' hne_yx)).min' hD_yx =
      ⟨1, by omega⟩ := by
    have : coverageSymmDiff y x ((differingThresholds y x).max' hne_yx) =
        {(⟨1, by omega⟩ : Fin 2)} := by
      rw [hmax_yx, hcsd_comm, h_csd_val]
    rw [Finset.min'_of_eq this hD_yx ⟨_, mem_singleton.mpr rfl⟩]
    exact Finset.min'_singleton _
  -- r* = ⟨1,_⟩ ∈ H₃(y)
  have hmem_y : (coverageSymmDiff y x ((differingThresholds y x).max' hne_yx)).min' hD_yx ∈
      coverageSet y ((differingThresholds y x).max' hne_yx) := by
    rw [hmin_sd, hmax_yx, mem_coverageSet]
    change (3 : ℝ) ≤ y ⟨1, by omega⟩
    simp [y, Matrix.cons_val_one, Matrix.head_cons]
  -- NDTC(y, x) gives ¬ strictPart R x y
  exact (hNDTC y x hyx hne_yx hD_yx hmem_y) hFOSDxy
