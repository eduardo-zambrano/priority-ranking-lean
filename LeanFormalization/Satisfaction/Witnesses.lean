/-
  PriorityRanking.Satisfaction.Witnesses
  Bridge lemmas and concrete witness facts for the NUTC/NDTC violation
  theorems in the satisfaction files.

  Key observation: for a pair (x, y), the hypotheses of NUTC are precisely
  `PPROT_strict x y`, and the hypotheses of NDTC are precisely
  `QPROT_strict x y`. So a rule R violates NUTC as soon as some pair has
  `PPROT_strict x y` while `strictPart R y x`, and dually for NDTC.
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms

open Finset

set_option linter.unusedSimpArgs false

/-! ## Bridge lemmas -/

/-- The NUTC hypotheses for a pair (x, y) are precisely `PPROT_strict x y`:
    if a preference satisfies NUTC and P-PROT strictly prefers x to y,
    the preference cannot strictly prefer y to x. -/
theorem not_strict_of_NUTC {n : ℕ} {R : PrefRel n} (h : Ax_NUTC R) {x y : Vec n}
    (hxy : x ≠ y) (hp : PPROT_strict x y) : ¬ strictPart R y x := by
  obtain ⟨hne, hD, hmem⟩ := hp
  exact h x y hxy hne hD hmem

/-- The NDTC hypotheses for a pair (x, y) are precisely `QPROT_strict x y`:
    if a preference satisfies NDTC and Q-PROT strictly prefers x to y,
    the preference cannot strictly prefer y to x. -/
theorem not_strict_of_NDTC {n : ℕ} {R : PrefRel n} (h : Ax_NDTC R) {x y : Vec n}
    (hxy : x ≠ y) (hq : QPROT_strict x y) : ¬ strictPart R y x := by
  obtain ⟨hne, hD, hmem⟩ := hq
  exact h x y hxy hne hD hmem

/-! ## Concrete P-PROT witnesses (lowest differing threshold) -/

/-- P-PROT strictly prefers (1,1) to (3,0): the lowest differing threshold is 1,
    the symmetric difference there is {1}, and state 1 is covered by (1,1). -/
theorem pprot_strict_11_30 : PPROT_strict (![1, 1] : Vec 2) ![3, 0] := by
  have h1_dt : (1 : ℝ) ∈ differingThresholds (![1, 1] : Vec 2) ![3, 0] := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨0, by omega⟩, by simp [Matrix.cons_val_zero]⟩
    · intro heq
      have h1x : (⟨1, by omega⟩ : Fin 2) ∈ coverageSet (![1, 1] : Vec 2) 1 := by
        rw [mem_coverageSet]; simp [Matrix.cons_val_one, Matrix.head_cons]
      rw [heq, mem_coverageSet] at h1x
      have : (![3, 0] : Vec 2) ⟨1, by omega⟩ = (0 : ℝ) := by
        simp [Matrix.cons_val_one, Matrix.head_cons]
      linarith
  exact pprot_strict_of_data 1 h1_dt
    (by -- ∀ b ∈ differingThresholds, 1 ≤ b
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, hb_diff⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i
      · simp [Matrix.cons_val_zero]  -- b = 1
      · simp [Matrix.cons_val_one, Matrix.head_cons]  -- b = 1
      · norm_num [Matrix.cons_val_zero]  -- b = 3: 1 ≤ 3
      · -- b = 0: coverage sets agree at 0
        exfalso; apply hb_diff; ext ⟨j, hj⟩; simp only [mem_coverageSet]
        interval_cases j <;>
          norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
    ⟨1, by omega⟩
    (by -- ⟨1,_⟩ ∈ coverageSymmDiff at threshold 1
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [Matrix.cons_val_one, Matrix.head_cons]
      · norm_num [Matrix.cons_val_one, Matrix.head_cons])
    (by -- minimality of ⟨1,_⟩ in the symmetric difference
      intro s hsmem
      fin_cases s
      · exfalso
        simp only [coverageSymmDiff, Finset.mem_symmDiff, mem_coverageSet] at hsmem
        norm_num [Matrix.cons_val_zero] at hsmem
      · exact le_refl _)
    (by rw [mem_coverageSet]; simp [Matrix.cons_val_one, Matrix.head_cons])

/-- P-PROT strictly prefers (1,1) to (2,0): the lowest differing threshold is 1,
    the symmetric difference there is {1}, and state 1 is covered by (1,1). -/
theorem pprot_strict_11_20 : PPROT_strict (![1, 1] : Vec 2) ![2, 0] := by
  have h1_dt : (1 : ℝ) ∈ differingThresholds (![1, 1] : Vec 2) ![2, 0] := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨0, by omega⟩, by simp [Matrix.cons_val_zero]⟩
    · intro heq
      have h1x : (⟨1, by omega⟩ : Fin 2) ∈ coverageSet (![1, 1] : Vec 2) 1 := by
        rw [mem_coverageSet]; simp [Matrix.cons_val_one, Matrix.head_cons]
      rw [heq, mem_coverageSet] at h1x
      have : (![2, 0] : Vec 2) ⟨1, by omega⟩ = (0 : ℝ) := by
        simp [Matrix.cons_val_one, Matrix.head_cons]
      linarith
  exact pprot_strict_of_data 1 h1_dt
    (by
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, hb_diff⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i
      · simp [Matrix.cons_val_zero]  -- b = 1
      · simp [Matrix.cons_val_one, Matrix.head_cons]  -- b = 1
      · norm_num [Matrix.cons_val_zero]  -- b = 2: 1 ≤ 2
      · -- b = 0: coverage sets agree at 0
        exfalso; apply hb_diff; ext ⟨j, hj⟩; simp only [mem_coverageSet]
        interval_cases j <;>
          norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
    ⟨1, by omega⟩
    (by
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [Matrix.cons_val_one, Matrix.head_cons]
      · norm_num [Matrix.cons_val_one, Matrix.head_cons])
    (by
      intro s hsmem
      fin_cases s
      · exfalso
        simp only [coverageSymmDiff, Finset.mem_symmDiff, mem_coverageSet] at hsmem
        norm_num [Matrix.cons_val_zero] at hsmem
      · exact le_refl _)
    (by rw [mem_coverageSet]; simp [Matrix.cons_val_one, Matrix.head_cons])

/-- P-PROT strictly prefers (2,2) to (3,0): the lowest differing threshold is 2,
    the symmetric difference there is {1}, and state 1 is covered by (2,2). -/
theorem pprot_strict_22_30 : PPROT_strict (![2, 2] : Vec 2) ![3, 0] := by
  have h2_dt : (2 : ℝ) ∈ differingThresholds (![2, 2] : Vec 2) ![3, 0] := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨0, by omega⟩, by simp [Matrix.cons_val_zero]⟩
    · intro heq
      have h1x : (⟨1, by omega⟩ : Fin 2) ∈ coverageSet (![2, 2] : Vec 2) 2 := by
        rw [mem_coverageSet]; simp [Matrix.cons_val_one, Matrix.head_cons]
      rw [heq, mem_coverageSet] at h1x
      have : (![3, 0] : Vec 2) ⟨1, by omega⟩ = (0 : ℝ) := by
        simp [Matrix.cons_val_one, Matrix.head_cons]
      linarith
  exact pprot_strict_of_data 2 h2_dt
    (by
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, hb_diff⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i
      · simp [Matrix.cons_val_zero]  -- b = 2
      · simp [Matrix.cons_val_one, Matrix.head_cons]  -- b = 2
      · norm_num [Matrix.cons_val_zero]  -- b = 3: 2 ≤ 3
      · -- b = 0: coverage sets agree at 0
        exfalso; apply hb_diff; ext ⟨j, hj⟩; simp only [mem_coverageSet]
        interval_cases j <;>
          norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
    ⟨1, by omega⟩
    (by
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [Matrix.cons_val_one, Matrix.head_cons]
      · norm_num [Matrix.cons_val_one, Matrix.head_cons])
    (by
      intro s hsmem
      fin_cases s
      · exfalso
        simp only [coverageSymmDiff, Finset.mem_symmDiff, mem_coverageSet] at hsmem
        norm_num [Matrix.cons_val_zero] at hsmem
      · exact le_refl _)
    (by rw [mem_coverageSet]; simp [Matrix.cons_val_one, Matrix.head_cons])

/-! ## Concrete Q-PROT witnesses (highest differing threshold) -/

/-- Q-PROT strictly prefers (3,0) to (1,1): the highest differing threshold is 3,
    the symmetric difference there is {0}, and state 0 is covered by (3,0). -/
theorem qprot_strict_30_11 : QPROT_strict (![3, 0] : Vec 2) ![1, 1] := by
  have h3_dt : (3 : ℝ) ∈ differingThresholds (![3, 0] : Vec 2) ![1, 1] := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨0, by omega⟩, by simp [Matrix.cons_val_zero]⟩
    · intro heq
      have h0x : (⟨0, by omega⟩ : Fin 2) ∈ coverageSet (![3, 0] : Vec 2) 3 := by
        rw [mem_coverageSet]; simp [Matrix.cons_val_zero]
      rw [heq, mem_coverageSet] at h0x
      have : (![1, 1] : Vec 2) ⟨0, by omega⟩ = (1 : ℝ) := by
        simp [Matrix.cons_val_zero]
      linarith
  exact qprot_strict_of_data 3 h3_dt
    (by -- ∀ b ∈ differingThresholds, b ≤ 3
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, _⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i <;>
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
    ⟨0, by omega⟩
    (by
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [Matrix.cons_val_zero]
      · norm_num [Matrix.cons_val_zero])
    (by intro s _; exact Fin.zero_le s)
    (by rw [mem_coverageSet]; simp [Matrix.cons_val_zero])

/-- Q-PROT strictly prefers (3,0) to (2,2): the highest differing threshold is 3,
    the symmetric difference there is {0}, and state 0 is covered by (3,0). -/
theorem qprot_strict_30_22 : QPROT_strict (![3, 0] : Vec 2) ![2, 2] := by
  have h3_dt : (3 : ℝ) ∈ differingThresholds (![3, 0] : Vec 2) ![2, 2] := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨0, by omega⟩, by simp [Matrix.cons_val_zero]⟩
    · intro heq
      have h0x : (⟨0, by omega⟩ : Fin 2) ∈ coverageSet (![3, 0] : Vec 2) 3 := by
        rw [mem_coverageSet]; simp [Matrix.cons_val_zero]
      rw [heq, mem_coverageSet] at h0x
      have : (![2, 2] : Vec 2) ⟨0, by omega⟩ = (2 : ℝ) := by
        simp [Matrix.cons_val_zero]
      linarith
  exact qprot_strict_of_data 3 h3_dt
    (by
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, _⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i <;>
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
    ⟨0, by omega⟩
    (by
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [Matrix.cons_val_zero]
      · norm_num [Matrix.cons_val_zero])
    (by intro s _; exact Fin.zero_le s)
    (by rw [mem_coverageSet]; simp [Matrix.cons_val_zero])

/-- Q-PROT strictly prefers (1,3) to (2,2): the highest differing threshold is 3,
    the symmetric difference there is {1}, and state 1 is covered by (1,3). -/
theorem qprot_strict_13_22 : QPROT_strict (![1, 3] : Vec 2) ![2, 2] := by
  have h3_dt : (3 : ℝ) ∈ differingThresholds (![1, 3] : Vec 2) ![2, 2] := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨1, by omega⟩, by simp [Matrix.cons_val_one, Matrix.head_cons]⟩
    · intro heq
      have h1x : (⟨1, by omega⟩ : Fin 2) ∈ coverageSet (![1, 3] : Vec 2) 3 := by
        rw [mem_coverageSet]; simp [Matrix.cons_val_one, Matrix.head_cons]
      rw [heq, mem_coverageSet] at h1x
      have : (![2, 2] : Vec 2) ⟨1, by omega⟩ = (2 : ℝ) := by
        simp [Matrix.cons_val_one, Matrix.head_cons]
      linarith
  exact qprot_strict_of_data 3 h3_dt
    (by
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, _⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i <;>
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
    ⟨1, by omega⟩
    (by
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [Matrix.cons_val_one, Matrix.head_cons]
      · norm_num [Matrix.cons_val_one, Matrix.head_cons])
    (by
      intro s hsmem
      fin_cases s
      · exfalso
        simp only [coverageSymmDiff, Finset.mem_symmDiff, mem_coverageSet] at hsmem
        norm_num [Matrix.cons_val_zero] at hsmem
      · exact le_refl _)
    (by rw [mem_coverageSet]; simp [Matrix.cons_val_one, Matrix.head_cons])

/-- Q-PROT strictly prefers (0,3) to (2,1): the highest differing threshold is 3,
    the symmetric difference there is {1}, and state 1 is covered by (0,3). -/
theorem qprot_strict_03_21 : QPROT_strict (![0, 3] : Vec 2) ![2, 1] := by
  have h3_dt : (3 : ℝ) ∈ differingThresholds (![0, 3] : Vec 2) ![2, 1] := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨1, by omega⟩, by simp [Matrix.cons_val_one, Matrix.head_cons]⟩
    · intro heq
      have h1x : (⟨1, by omega⟩ : Fin 2) ∈ coverageSet (![0, 3] : Vec 2) 3 := by
        rw [mem_coverageSet]; simp [Matrix.cons_val_one, Matrix.head_cons]
      rw [heq, mem_coverageSet] at h1x
      have : (![2, 1] : Vec 2) ⟨1, by omega⟩ = (1 : ℝ) := by
        simp [Matrix.cons_val_one, Matrix.head_cons]
      linarith
  exact qprot_strict_of_data 3 h3_dt
    (by
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, _⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i <;>
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
    ⟨1, by omega⟩
    (by
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [Matrix.cons_val_one, Matrix.head_cons]
      · norm_num [Matrix.cons_val_one, Matrix.head_cons])
    (by
      intro s hsmem
      fin_cases s
      · exfalso
        simp only [coverageSymmDiff, Finset.mem_symmDiff, mem_coverageSet] at hsmem
        norm_num [Matrix.cons_val_zero] at hsmem
      · exact le_refl _)
    (by rw [mem_coverageSet]; simp [Matrix.cons_val_one, Matrix.head_cons])
