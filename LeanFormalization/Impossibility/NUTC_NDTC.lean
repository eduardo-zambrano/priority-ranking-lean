/-
  LeanFormalization.Impossibility.NUTC_NDTC
  Impossibility: C, T, PD, NUTC, and NDTC are jointly unsatisfiable (n = 2).
  (Paper: "NUTC and NDTC cannot be reconciled" — the third impossibility theorem.)

  Counterexample: x = (0, 2), y = (1, 1), z = (3/2, 1)  [0-based indices below].

  Step 1: differingThresholds x y = {1, 2}, with minimum 1.
    At threshold 1: H₁(x) = {1}, H₁(y) = {0, 1}, symmdiff = {0}, r* = 0 ∈ H₁(y).
    NUTC applied to (y, x) gives ¬(x ≻ y); with Completeness, R y x.
  Step 2: z Pareto-dominates y (strictly in coordinate 0), so PD gives z ≻ y;
    with Transitivity and R y x, z ≻ x.
  Step 3: differingThresholds x z = {1, 3/2, 2}, with maximum 2.
    At threshold 2: H₂(x) = {1}, H₂(z) = ∅, symmdiff = {1}, r* = 1 ∈ H₂(x).
    NDTC applied to (x, z) gives ¬(z ≻ x). Contradiction.

  Every proper subset of {C, T, PD, NUTC, NDTC} is satisfiable
  (P-PROT, Q-PROT, total indifference, Pareto partial order, dominance-only
  complete relation), so this is a minimal inconsistent set.
-/

import LeanFormalization.Defs.Axioms

open Finset

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-- C, T, PD, NUTC, and NDTC are jointly unsatisfiable (n = 2).
    Within the level-first family, a choice of scanning direction is forced. -/
theorem NUTC_NDTC_impossible (R : PrefRel 2) :
    Ax_C R → Ax_T R → Ax_PD R → Ax_NUTC R → Ax_NDTC R → False := by
  intro hC hT hPD hNUTC hNDTC
  let x : Vec 2 := ![0, 2]
  let y : Vec 2 := ![1, 1]
  let z : Vec 2 := ![3/2, 1]
  have hxy : x ≠ y := by
    intro h; have := congr_fun h ⟨0, by omega⟩
    simp [x, y, Matrix.cons_val_zero] at this
  have hyx : y ≠ x := Ne.symm hxy
  have hxz : x ≠ z := by
    intro h; have := congr_fun h ⟨1, by omega⟩
    simp [x, z, Matrix.cons_val_one, Matrix.head_cons] at this
  -- ## Step 1: NUTC on (y, x) at min differing threshold 1 gives ¬(x ≻ y)
  have hne := differingThresholds_nonempty x y hxy
  -- 1 ∈ differingThresholds x y
  have h1_dt : (1 : ℝ) ∈ differingThresholds x y := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inr ⟨⟨0, by omega⟩, by simp [y, Matrix.cons_val_zero]⟩
    · intro heq
      have h0 : (⟨0, by omega⟩ : Fin 2) ∈ coverageSet y 1 := by
        rw [mem_coverageSet]; show (1 : ℝ) ≤ y ⟨0, by omega⟩
        simp [y, Matrix.cons_val_zero]
      rw [← heq, mem_coverageSet] at h0
      have : x (⟨0, by omega⟩ : Fin 2) = (0 : ℝ) := by
        simp [x, Matrix.cons_val_zero]
      linarith
  -- min(differingThresholds x y) = 1
  have hmin_eq : (differingThresholds x y).min' hne = 1 := by
    apply le_antisymm (Finset.min'_le _ _ h1_dt)
    apply Finset.le_min'; intro b hb
    rw [differingThresholds, Finset.mem_filter] at hb
    obtain ⟨hb_tv, hb_diff⟩ := hb
    simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
    rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i
    · -- b = x₀ = 0: coverage sets are equal at 0, contradiction
      exfalso; apply hb_diff; ext ⟨j, hj⟩; simp only [mem_coverageSet]
      interval_cases j <;>
        simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> norm_num
    · -- b = x₁ = 2: 1 ≤ 2
      simp [x, Matrix.cons_val_one, Matrix.head_cons] <;> norm_num
    · -- b = y₀ = 1: 1 ≤ 1
      simp [y, Matrix.cons_val_zero]
    · -- b = y₁ = 1: 1 ≤ 1
      simp [y, Matrix.cons_val_one, Matrix.head_cons]
  -- Transport to (y, x) via symmetry
  have hdt_comm : differingThresholds y x = differingThresholds x y :=
    differingThresholds_comm y x
  have hne_yx : (differingThresholds y x).Nonempty := hdt_comm ▸ hne
  have hmin_yx : (differingThresholds y x).min' hne_yx = 1 := by
    rw [Finset.min'_of_eq hdt_comm hne_yx hne]; exact hmin_eq
  have ha_ne_min := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  have hD_min := symmDiff_nonempty_of_ne x y _ ha_ne_min
  have hcsd_comm1 := coverageSymmDiff_comm y x 1
  have hcsd_eq_min := congr_arg (coverageSymmDiff x y) hmin_eq
  have hD1 : (coverageSymmDiff x y 1).Nonempty := hcsd_eq_min ▸ hD_min
  have hD_yx : (coverageSymmDiff y x ((differingThresholds y x).min' hne_yx)).Nonempty := by
    rw [hmin_yx, hcsd_comm1]; exact hD1
  -- Symmetric difference at 1 = {⟨0,_⟩}
  have h_csd_val1 : coverageSymmDiff x y 1 = {(⟨0, by omega⟩ : Fin 2)} := by
    ext ⟨j, hj⟩; simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet, mem_singleton,
      Fin.ext_iff]
    interval_cases j <;>
      simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> norm_num
  have hmin_sd1 : (coverageSymmDiff y x ((differingThresholds y x).min' hne_yx)).min' hD_yx =
      ⟨0, by omega⟩ := by
    have hval : coverageSymmDiff y x ((differingThresholds y x).min' hne_yx) =
        {(⟨0, by omega⟩ : Fin 2)} := by
      rw [hmin_yx, hcsd_comm1, h_csd_val1]
    rw [Finset.min'_of_eq hval hD_yx ⟨_, mem_singleton.mpr rfl⟩]
    exact Finset.min'_singleton _
  -- r* = ⟨0,_⟩ ∈ H₁(y)
  have hmem_y : (coverageSymmDiff y x ((differingThresholds y x).min' hne_yx)).min' hD_yx ∈
      coverageSet y ((differingThresholds y x).min' hne_yx) := by
    rw [hmin_sd1, hmin_yx, mem_coverageSet]
    change (1 : ℝ) ≤ y ⟨0, by omega⟩
    simp [y, Matrix.cons_val_zero]
  have hnot_sxy : ¬ strictPart R x y := hNUTC y x hyx hne_yx hD_yx hmem_y
  -- With Completeness: R y x
  have hRyx : R y x := by
    rcases hC x y with h | h
    · by_contra hn; exact hnot_sxy ⟨h, hn⟩
    · exact h
  -- ## Step 2: PD gives z ≻ y; with T, z ≻ x
  have hge_zy : ∀ i : Fin 2, z i ≥ y i := by
    intro i; fin_cases i <;>
      simp [z, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> norm_num
  have hstrict_zy0 : z ⟨0, by omega⟩ > y ⟨0, by omega⟩ := by
    simp [z, y, Matrix.cons_val_zero] <;> norm_num
  have hPD_zy : strictPart R z y := hPD z y hge_zy ⟨⟨0, by omega⟩, hstrict_zy0⟩
  have hRzx : R z x := hT z y x hPD_zy.1 hRyx
  have hnRxz : ¬ R x z := fun h => hPD_zy.2 (hT y x z hRyx h)
  have hs_zx : strictPart R z x := ⟨hRzx, hnRxz⟩
  -- ## Step 3: NDTC on (x, z) at max differing threshold 2 gives ¬(z ≻ x)
  have hne_xz := differingThresholds_nonempty x z hxz
  -- 2 ∈ differingThresholds x z
  have h2_dt_xz : (2 : ℝ) ∈ differingThresholds x z := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨1, by omega⟩, by simp [x, Matrix.cons_val_one, Matrix.head_cons]⟩
    · intro heq
      have h1 : (⟨1, by omega⟩ : Fin 2) ∈ coverageSet x 2 := by
        rw [mem_coverageSet]; show (2 : ℝ) ≤ x ⟨1, by omega⟩
        simp [x, Matrix.cons_val_one, Matrix.head_cons]
      rw [heq, mem_coverageSet] at h1
      have : z (⟨1, by omega⟩ : Fin 2) = (1 : ℝ) := by
        simp [z, Matrix.cons_val_one, Matrix.head_cons]
      linarith
  -- max(differingThresholds x z) = 2
  have hmax_xz : (differingThresholds x z).max' hne_xz = 2 := by
    apply le_antisymm
    · apply Finset.max'_le; intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb
      obtain ⟨hb_tv, _⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i <;>
        simp [x, z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> norm_num
    · exact Finset.le_max' _ _ h2_dt_xz
  have ha_ne_xz := (Finset.mem_filter.mp (Finset.max'_mem _ hne_xz)).2
  have hD_xz := symmDiff_nonempty_of_ne x z _ ha_ne_xz
  -- Symmetric difference at 2 = {⟨1,_⟩}
  have h_csd_val_xz : coverageSymmDiff x z 2 = {(⟨1, by omega⟩ : Fin 2)} := by
    ext ⟨j, hj⟩; simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet, mem_singleton,
      Fin.ext_iff]
    interval_cases j <;>
      simp [x, z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> norm_num
  have hmin_sd_xz : (coverageSymmDiff x z ((differingThresholds x z).max' hne_xz)).min' hD_xz =
      ⟨1, by omega⟩ := by
    have hval : coverageSymmDiff x z ((differingThresholds x z).max' hne_xz) =
        {(⟨1, by omega⟩ : Fin 2)} := by
      rw [hmax_xz]; exact h_csd_val_xz
    rw [Finset.min'_of_eq hval hD_xz ⟨_, mem_singleton.mpr rfl⟩]
    exact Finset.min'_singleton _
  -- r* = ⟨1,_⟩ ∈ H₂(x)
  have hmem_xz : (coverageSymmDiff x z ((differingThresholds x z).max' hne_xz)).min' hD_xz ∈
      coverageSet x ((differingThresholds x z).max' hne_xz) := by
    rw [hmin_sd_xz, hmax_xz, mem_coverageSet]
    change (2 : ℝ) ≤ x ⟨1, by omega⟩
    simp [x, Matrix.cons_val_one, Matrix.head_cons]
  -- NDTC(x, z) gives ¬(z ≻ x) — contradiction with Step 2
  exact (hNDTC x z hxz hne_xz hD_xz hmem_xz) hs_zx
