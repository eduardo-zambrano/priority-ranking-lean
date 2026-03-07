/-
  PriorityRanking.Satisfaction.PPROT
  Which axioms P-PROT satisfies and violates.

  Satisfies: C, LTSF (from characterization); T, PD, CST, CX, CVG
  Violates: TSM, TSI, TM, TI, NCA
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms
import LeanFormalization.Characterizations.PPROT

/-! ## P-PROT satisfies C and LTSF (from Characterizations/PPROT.lean) -/

-- PPROT_satisfies_C and PPROT_satisfies_LTSF are exported from
-- LeanFormalization.Characterizations.PPROT

open Finset

set_option linter.unusedSimpArgs false

/-! ### Reusable tactic for "b = v_i, coverage sets equal, contradiction" -/

-- Common pattern: show that at a threshold equal to some component value,
-- the coverage sets are actually equal, contradicting membership in differingThresholds.
-- We inline this each time since the vectors differ.

/-! ## P-PROT violates TM -/

/-- P-PROT violates Total Monotonicity: y=(0,3) has higher total than x=(2,0),
    but P-PROT prefers x (threshold 2: H₂(x)={0}, H₂(y)=∅, min=0 ∈ H₂(x)). -/
theorem PPROT_violates_TM : ¬ Ax_TM (@PPROT 2) := by
  intro hTM
  let x : Vec 2 := ![2, 0]
  let y : Vec 2 := ![0, 3]
  have htotal : totalSum y > totalSum x := by
    simp only [totalSum]; rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num
  have hstrict := hTM y x htotal
  have hxy : x ≠ y := by
    intro h; have := congr_fun h ⟨0, by omega⟩; simp [x, y, Matrix.cons_val_zero] at this
  have h2_dt : (2 : ℝ) ∈ differingThresholds x y := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨0, by omega⟩, by simp [x, Matrix.cons_val_zero]⟩
    · intro heq
      have h0x : (⟨0, by omega⟩ : Fin 2) ∈ coverageSet x 2 := by
        rw [mem_coverageSet]; simp [x, Matrix.cons_val_zero]
      rw [heq, mem_coverageSet] at h0x
      have : y (⟨0, by omega⟩ : Fin 2) = (0 : ℝ) := by simp [y, Matrix.cons_val_zero]
      linarith
  have hpprot : PPROT_strict x y := pprot_strict_of_data 2 h2_dt
    (by -- ∀ b ∈ differingThresholds, 2 ≤ b
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, hb_diff⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i
      · -- b = x₀ = 2: 2 ≤ 2
        simp [x, Matrix.cons_val_zero]
      · -- b = x₁ = 0: equal coverage sets
        exfalso; apply hb_diff; ext ⟨j, hj⟩; simp only [mem_coverageSet]
        interval_cases j <;> simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      · -- b = y₀ = 0: equal coverage sets
        exfalso; apply hb_diff; ext ⟨j, hj⟩; simp only [mem_coverageSet]
        interval_cases j <;> simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      · -- b = y₁ = 3: 2 ≤ 3
        simp [y, Matrix.cons_val_one, Matrix.head_cons]; norm_num)
    ⟨0, by omega⟩  -- r = state 0
    (by -- 0 ∈ coverageSymmDiff x y 2
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [x, Matrix.cons_val_zero]
      · simp [y, Matrix.cons_val_zero])
    (by intro s _; exact Fin.zero_le s)
    (by rw [mem_coverageSet]; simp [x, Matrix.cons_val_zero])
  exact hstrict.2 (Or.inr hpprot)

/-! ## P-PROT violates TI -/

/-- P-PROT violates Total Indifference: (1,0) and (0,1) have equal totals
    but P-PROT strictly prefers (1,0). -/
theorem PPROT_violates_TI : ¬ Ax_TI (@PPROT 2) := by
  intro hTI
  let x : Vec 2 := ![1, 0]
  let y : Vec 2 := ![0, 1]
  have htotal : totalSum x = totalSum y := by
    simp only [totalSum]; rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hindiff := hTI x y htotal
  have hxy : x ≠ y := by
    intro h; have := congr_fun h ⟨0, by omega⟩; simp [x, y, Matrix.cons_val_zero] at this
  have h1_dt : (1 : ℝ) ∈ differingThresholds x y := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨0, by omega⟩, by simp [x, Matrix.cons_val_zero]⟩
    · intro heq
      have h0x : (⟨0, by omega⟩ : Fin 2) ∈ coverageSet x 1 := by
        rw [mem_coverageSet]; simp [x, Matrix.cons_val_zero]
      rw [heq, mem_coverageSet] at h0x
      have : y (⟨0, by omega⟩ : Fin 2) = (0 : ℝ) := by simp [y, Matrix.cons_val_zero]
      linarith
  have hpprot : PPROT_strict x y := pprot_strict_of_data 1 h1_dt
    (by
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, hb_diff⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i
      · simp [x, Matrix.cons_val_zero]  -- x₀ = 1
      · exfalso; apply hb_diff; ext ⟨j, hj⟩; simp only [mem_coverageSet]
        interval_cases j <;> simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      · exfalso; apply hb_diff; ext ⟨j, hj⟩; simp only [mem_coverageSet]
        interval_cases j <;> simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      · simp [y, Matrix.cons_val_one, Matrix.head_cons])  -- y₁ = 1
    ⟨0, by omega⟩
    (by
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [x, Matrix.cons_val_zero]
      · simp [y, Matrix.cons_val_zero])
    (by intro s _; exact Fin.zero_le s)
    (by rw [mem_coverageSet]; simp [x, Matrix.cons_val_zero])
  -- PPROT_strict x y contradicts indiffPart (which requires R y x)
  exact (PPROT_strictPart_of_strict hxy hpprot).2 hindiff.2

/-! ## P-PROT violates TSM -/

/-- P-PROT violates Top-State Monotonicity: x=(2,0), y=(1,3). x₀=2>1=y₀,
    but PPROT prefers y (threshold 1: H₁(y)⊃H₁(x), symmdiff={1}, min=1 ∈ H₁(y)). -/
theorem PPROT_violates_TSM : ¬ Ax_TSM (@PPROT 2) := by
  intro hTSM
  let x : Vec 2 := ![2, 0]
  let y : Vec 2 := ![1, 3]
  have hx0 : x ⟨0, by omega⟩ > y ⟨0, by omega⟩ := by simp [x, y, Matrix.cons_val_zero]
  have hstrict := hTSM x y hx0
  -- But PPROT_strict y x: at threshold 1, H₁(y)={0,1}, H₁(x)={0}, symmdiff={1}, min=1 ∈ H₁(y)
  have hyx : y ≠ x := by
    intro h; have := congr_fun h ⟨0, by omega⟩; simp [x, y, Matrix.cons_val_zero] at this
  have h1_dt : (1 : ℝ) ∈ differingThresholds y x := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨0, by omega⟩, by simp [y, Matrix.cons_val_zero]⟩
    · intro heq
      have h1y : (⟨1, by omega⟩ : Fin 2) ∈ coverageSet y 1 := by
        rw [mem_coverageSet]
        simp [y, Matrix.cons_val_one, Matrix.head_cons]
      rw [heq, mem_coverageSet] at h1y
      have : x (⟨1, by omega⟩ : Fin 2) = (0 : ℝ) := by
        simp [x, Matrix.cons_val_one, Matrix.head_cons]
      linarith
  have hpprot : PPROT_strict y x := pprot_strict_of_data 1 h1_dt
    (by
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, hb_diff⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i
      · simp [y, Matrix.cons_val_zero]  -- y₀ = 1
      · simp [y, Matrix.cons_val_one, Matrix.head_cons]  -- y₁ = 3: 1 ≤ 3
      · simp [x, Matrix.cons_val_zero]  -- x₀ = 2: 1 ≤ 2
      · -- x₁ = 0: coverage sets equal at 0
        exfalso; apply hb_diff; ext ⟨j, hj⟩; simp only [mem_coverageSet]
        interval_cases j <;> simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
    ⟨1, by omega⟩
    (by
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [y, Matrix.cons_val_one, Matrix.head_cons]
      · simp [x, Matrix.cons_val_one, Matrix.head_cons])
    (by -- ∀ s ∈ coverageSymmDiff, ⟨1,_⟩ ≤ s
      intro ⟨s, hs⟩ hmem
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet, Fin.le_iff_val_le_val] at hmem ⊢
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> interval_cases s <;>
        simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h1 h2 ⊢)
    (by rw [mem_coverageSet]; simp [y, Matrix.cons_val_one, Matrix.head_cons])
  exact hstrict.2 (Or.inr hpprot)

/-! ## P-PROT violates TSI -/

/-- P-PROT violates Top-State Indifference: x=(1,2), y=(1,0). x₀=y₀=1,
    but PPROT strictly prefers x (threshold 1: symmdiff={1}, min=1 ∈ H₁(x)). -/
theorem PPROT_violates_TSI : ¬ Ax_TSI (@PPROT 2) := by
  intro hTSI
  let x : Vec 2 := ![1, 2]
  let y : Vec 2 := ![1, 0]
  have hx0 : x ⟨0, by omega⟩ = y ⟨0, by omega⟩ := by simp [x, y, Matrix.cons_val_zero]
  have hindiff := hTSI x y hx0
  have hxy : x ≠ y := by
    intro h; have := congr_fun h ⟨1, by omega⟩
    simp [x, y, Matrix.cons_val_one, Matrix.head_cons] at this
  have h1_dt : (1 : ℝ) ∈ differingThresholds x y := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨0, by omega⟩, by simp [x, Matrix.cons_val_zero]⟩
    · intro heq
      have h1x : (⟨1, by omega⟩ : Fin 2) ∈ coverageSet x 1 := by
        rw [mem_coverageSet]; simp [x, Matrix.cons_val_one, Matrix.head_cons]
      rw [heq, mem_coverageSet] at h1x
      have : y (⟨1, by omega⟩ : Fin 2) = (0 : ℝ) := by
        simp [y, Matrix.cons_val_one, Matrix.head_cons]
      linarith
  have hpprot : PPROT_strict x y := pprot_strict_of_data 1 h1_dt
    (by
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, hb_diff⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i
      · simp [x, Matrix.cons_val_zero]  -- x₀ = 1
      · simp [x, Matrix.cons_val_one, Matrix.head_cons]  -- x₁ = 2: 1 ≤ 2
      · simp [y, Matrix.cons_val_zero]  -- y₀ = 1
      · -- y₁ = 0: coverage sets equal at 0
        exfalso; apply hb_diff; ext ⟨j, hj⟩; simp only [mem_coverageSet]
        interval_cases j <;> simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
    ⟨1, by omega⟩
    (by
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [x, Matrix.cons_val_one, Matrix.head_cons]
      · simp [y, Matrix.cons_val_one, Matrix.head_cons])
    (by
      intro ⟨s, hs⟩ hmem
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet, Fin.le_iff_val_le_val] at hmem ⊢
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> interval_cases s <;>
        simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h1 h2 ⊢)
    (by rw [mem_coverageSet]; simp [x, Matrix.cons_val_one, Matrix.head_cons])
  exact (PPROT_strictPart_of_strict hxy hpprot).2 hindiff.2

/-! ## P-PROT violates NCA -/

/-- P-PROT violates NCA. Counterexample (n=3): x = (5,2,0), y = (5,1,1).
    At k=1: x₁ = 2 > 1 = y₁, x₀ = y₀ = 5. NCA says ¬strictPart PPROT y x.
    But P-PROT: threshold 1, H₁(y) = {0,1,2}, H₁(x) = {0,1}, D={2}, min=2 ∈ H₁(y),
    so PPROT_strict y x. -/
theorem PPROT_violates_NCA : ¬ Ax_NCA (@PPROT 3) := by
  intro hNCA
  let x : Vec 3 := ![5, 2, 0]
  let y : Vec 3 := ![5, 1, 1]
  have hk_eq : ∀ i : Fin 3, i < ⟨1, by omega⟩ → x i = y i := by
    intro ⟨i, hi⟩ hlt; simp [Fin.lt_def] at hlt
    interval_cases i
    · simp [x, y, Matrix.cons_val_zero]
    all_goals omega
  have hk_gt : x ⟨1, by omega⟩ > y ⟨1, by omega⟩ := by
    simp [x, y, Matrix.cons_val_one, Matrix.head_cons]
  have hy'_eq : ∀ i : Fin 3, i ≤ ⟨1, by omega⟩ → y i = y i := fun _ _ => rfl
  have hnca := hNCA x y ⟨1, by omega⟩ hk_eq hk_gt y hy'_eq
  -- Show PPROT_strict y x
  have hyx : y ≠ x := by
    intro h; have := congr_fun h ⟨1, by omega⟩
    simp [x, y, Matrix.cons_val_one, Matrix.head_cons] at this
  -- Access helpers for Fin 3 vectors
  have hx0 : x ⟨0, by omega⟩ = (5 : ℝ) := by simp [x, Matrix.cons_val_zero]
  have hx1 : x ⟨1, by omega⟩ = (2 : ℝ) := by simp [x, Matrix.cons_val_one, Matrix.head_cons]
  have hx2 : x ⟨2, by omega⟩ = (0 : ℝ) := by
    simp [x, Matrix.cons_val_one, Matrix.head_cons]
  have hy0 : y ⟨0, by omega⟩ = (5 : ℝ) := by simp [y, Matrix.cons_val_zero]
  have hy1' : y ⟨1, by omega⟩ = (1 : ℝ) := by simp [y, Matrix.cons_val_one, Matrix.head_cons]
  have hy2 : y ⟨2, by omega⟩ = (1 : ℝ) := by
    simp [y, Matrix.cons_val_one, Matrix.head_cons]
  have h1_dt : (1 : ℝ) ∈ differingThresholds y x := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨1, by omega⟩, hy1'⟩
    · intro heq
      have h2y : (⟨2, by omega⟩ : Fin 3) ∈ coverageSet y 1 := by
        rw [mem_coverageSet]; linarith [hy2]
      rw [heq, mem_coverageSet] at h2y; linarith [hx2]
  have hpprot : PPROT_strict y x := pprot_strict_of_data 1 h1_dt
    (by -- ∀ b ∈ differingThresholds y x, 1 ≤ b
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, hb_diff⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i
      · linarith [hy0]  -- b = y₀ = 5
      · linarith [hy1']  -- b = y₁ = 1
      · -- b = y₂ = 1
        linarith [hy2]
      · linarith [hx0]  -- b = x₀ = 5
      · linarith [hx1]  -- b = x₁ = 2
      · -- b = x₂ = 0: coverage sets equal at 0
        exfalso; apply hb_diff; ext ⟨j, hj⟩; simp only [mem_coverageSet]
        interval_cases j <;> constructor <;> intro h <;> linarith [hx0, hx1, hx2, hy0, hy1', hy2])
    ⟨2, by omega⟩
    (by -- ⟨2,_⟩ ∈ coverageSymmDiff y x 1
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left
      exact ⟨by linarith [hy2], by linarith [hx2]⟩)
    (by -- ∀ s ∈ coverageSymmDiff y x 1, ⟨2,_⟩ ≤ s
      intro ⟨s, hs⟩ hmem
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet, Fin.le_iff_val_le_val] at hmem ⊢
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- s ∈ H₁(y) \ H₁(x)
        interval_cases s
        · exfalso; exact h2 (by linarith [hx0])
        · exfalso; exact h2 (by linarith [hx1])
        · omega
      · -- s ∈ H₁(x) \ H₁(y)
        interval_cases s
        · exfalso; exact h2 (by linarith [hy0])
        · exfalso; exact h2 (by linarith [hy1'])
        · exfalso; exact h2 (by linarith [hx2]))
    (by rw [mem_coverageSet]; linarith [hy2])
  exact hnca (PPROT_strictPart_of_strict hyx hpprot)
