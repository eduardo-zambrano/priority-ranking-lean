/-
  PriorityRanking.Satisfaction.QPROT
  Which axioms Q-PROT satisfies and violates.

  Satisfies: C, HTSF (from characterization); T, PD, CST, CX, CVG
  Violates: TSM, TSI, TM, TI, NCA
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms
import LeanFormalization.Characterizations.QPROT

/-! ## Q-PROT satisfies C and HTSF (from Characterizations/QPROT.lean) -/

-- QPROT_satisfies_C and QPROT_satisfies_HTSF are exported from
-- LeanFormalization.Characterizations.QPROT

open Finset

set_option linter.unusedSimpArgs false

/-! ## Q-PROT violates TM -/

/-- Q-PROT violates Total Monotonicity: y=(2,2) has higher total than x=(3,0),
    but Q-PROT prefers x (max threshold 3: H₃(x)={0}, H₃(y)=∅). -/
theorem QPROT_violates_TM : ¬ Ax_TM (@QPROT 2) := by
  intro hTM
  let x : Vec 2 := ![3, 0]
  let y : Vec 2 := ![2, 2]
  have htotal : totalSum y > totalSum x := by
    simp only [totalSum]; rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num
  have hstrict := hTM y x htotal
  have hxy : x ≠ y := by
    intro h; have := congr_fun h ⟨0, by omega⟩; simp [x, y, Matrix.cons_val_zero] at this
  have h3_dt : (3 : ℝ) ∈ differingThresholds x y := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨0, by omega⟩, by simp [x, Matrix.cons_val_zero]⟩
    · intro heq
      have h0x : (⟨0, by omega⟩ : Fin 2) ∈ coverageSet x 3 := by
        rw [mem_coverageSet]; simp [x, Matrix.cons_val_zero]
      rw [heq, mem_coverageSet] at h0x
      have : y (⟨0, by omega⟩ : Fin 2) = (2 : ℝ) := by simp [y, Matrix.cons_val_zero]
      linarith
  have hqprot : QPROT_strict x y := qprot_strict_of_data 3 h3_dt
    (by -- ∀ b ∈ differingThresholds, b ≤ 3
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, _⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i <;>
        simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> norm_num)
    ⟨0, by omega⟩
    (by
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [x, Matrix.cons_val_zero]
      · simp [y, Matrix.cons_val_zero]; norm_num)
    (by intro s _; exact Fin.zero_le s)
    (by rw [mem_coverageSet]; simp [x, Matrix.cons_val_zero])
  exact hstrict.2 (Or.inr hqprot)

/-! ## Q-PROT violates TI -/

/-- Q-PROT violates Total Indifference: (2,0) and (1,1) have equal totals
    but Q-PROT strictly prefers (2,0). Max threshold 2: H₂(x)={0}, H₂(y)=∅. -/
theorem QPROT_violates_TI : ¬ Ax_TI (@QPROT 2) := by
  intro hTI
  let x : Vec 2 := ![2, 0]
  let y : Vec 2 := ![1, 1]
  have htotal : totalSum x = totalSum y := by
    simp only [totalSum]; rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num
  have hindiff := hTI x y htotal
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
      have : y (⟨0, by omega⟩ : Fin 2) = (1 : ℝ) := by simp [y, Matrix.cons_val_zero]
      linarith
  have hqprot : QPROT_strict x y := qprot_strict_of_data 2 h2_dt
    (by
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, _⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i <;>
        simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
    ⟨0, by omega⟩
    (by
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [x, Matrix.cons_val_zero]
      · simp [y, Matrix.cons_val_zero])
    (by intro s _; exact Fin.zero_le s)
    (by rw [mem_coverageSet]; simp [x, Matrix.cons_val_zero])
  exact (QPROT_strictPart_of_strict hxy hqprot).2 hindiff.2

/-! ## Q-PROT violates TSM -/

/-- Q-PROT violates Top-State Monotonicity: x=(2,0), y=(1,3). x₀=2>1=y₀,
    but QPROT prefers y (max threshold 3: H₃(y)={1}, H₃(x)=∅, min=1 ∈ H₃(y)). -/
theorem QPROT_violates_TSM : ¬ Ax_TSM (@QPROT 2) := by
  intro hTSM
  let x : Vec 2 := ![2, 0]
  let y : Vec 2 := ![1, 3]
  have hx0 : x ⟨0, by omega⟩ > y ⟨0, by omega⟩ := by simp [x, y, Matrix.cons_val_zero]
  have hstrict := hTSM x y hx0
  have hyx : y ≠ x := by
    intro h; have := congr_fun h ⟨0, by omega⟩; simp [x, y, Matrix.cons_val_zero] at this
  have h3_dt : (3 : ℝ) ∈ differingThresholds y x := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨1, by omega⟩, by simp [y, Matrix.cons_val_one, Matrix.head_cons]⟩
    · intro heq
      have h1y : (⟨1, by omega⟩ : Fin 2) ∈ coverageSet y 3 := by
        rw [mem_coverageSet]; simp [y, Matrix.cons_val_one, Matrix.head_cons]
      rw [heq, mem_coverageSet] at h1y
      have : x (⟨1, by omega⟩ : Fin 2) = (0 : ℝ) := by
        simp [x, Matrix.cons_val_one, Matrix.head_cons]
      linarith
  have hqprot : QPROT_strict y x := qprot_strict_of_data 3 h3_dt
    (by
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, _⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i <;>
        simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> norm_num)
    ⟨1, by omega⟩
    (by
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [y, Matrix.cons_val_one, Matrix.head_cons]
      · simp [x, Matrix.cons_val_one, Matrix.head_cons])
    (by
      intro ⟨s, hs⟩ hmem
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet,
        Fin.le_iff_val_le_val] at hmem ⊢
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> interval_cases s <;>
        simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons] at h1 h2 ⊢ <;> linarith)
    (by rw [mem_coverageSet]; simp [y, Matrix.cons_val_one, Matrix.head_cons])
  exact hstrict.2 (Or.inr hqprot)

/-! ## Q-PROT violates TSI -/

/-- Q-PROT violates Top-State Indifference: x=(1,2), y=(1,0). x₀=y₀=1,
    but QPROT strictly prefers x (max threshold 2: H₂(x)={1}, H₂(y)=∅). -/
theorem QPROT_violates_TSI : ¬ Ax_TSI (@QPROT 2) := by
  intro hTSI
  let x : Vec 2 := ![1, 2]
  let y : Vec 2 := ![1, 0]
  have hx0 : x ⟨0, by omega⟩ = y ⟨0, by omega⟩ := by simp [x, y, Matrix.cons_val_zero]
  have hindiff := hTSI x y hx0
  have hxy : x ≠ y := by
    intro h; have := congr_fun h ⟨1, by omega⟩
    simp [x, y, Matrix.cons_val_one, Matrix.head_cons] at this
  have h2_dt : (2 : ℝ) ∈ differingThresholds x y := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨1, by omega⟩, by simp [x, Matrix.cons_val_one, Matrix.head_cons]⟩
    · intro heq
      have h1x : (⟨1, by omega⟩ : Fin 2) ∈ coverageSet x 2 := by
        rw [mem_coverageSet]; simp [x, Matrix.cons_val_one, Matrix.head_cons]
      rw [heq, mem_coverageSet] at h1x
      have : y (⟨1, by omega⟩ : Fin 2) = (0 : ℝ) := by
        simp [y, Matrix.cons_val_one, Matrix.head_cons]
      linarith
  have hqprot : QPROT_strict x y := qprot_strict_of_data 2 h2_dt
    (by
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, _⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i <;>
        simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
    ⟨1, by omega⟩
    (by
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [x, Matrix.cons_val_one, Matrix.head_cons]
      · simp [y, Matrix.cons_val_one, Matrix.head_cons])
    (by
      intro ⟨s, hs⟩ hmem
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet,
        Fin.le_iff_val_le_val] at hmem ⊢
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> interval_cases s <;>
        simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons] at h1 h2 ⊢ <;> linarith)
    (by rw [mem_coverageSet]; simp [x, Matrix.cons_val_one, Matrix.head_cons])
  exact (QPROT_strictPart_of_strict hxy hqprot).2 hindiff.2

/-! ## Q-PROT violates NCA -/

/-- Q-PROT violates NCA. Counterexample (n=2): x=(1,0), y=(0,3).
    k=0: x₀=1>0=y₀, no coords above k=0. NCA says ¬strictPart QPROT y x.
    But QPROT: max threshold 3, H₃(y)={1}, H₃(x)=∅, min=1 ∈ H₃(y),
    so QPROT_strict y x. -/
theorem QPROT_violates_NCA : ¬ Ax_NCA (@QPROT 2) := by
  intro hNCA
  let x : Vec 2 := ![1, 0]
  let y : Vec 2 := ![0, 3]
  -- k = ⟨0, _⟩: x₀ = 1 > 0 = y₀, no coords above k
  have hk_eq : ∀ i : Fin 2, i < ⟨0, by omega⟩ → x i = y i := by
    intro i hi; exact absurd hi (not_lt.mpr (Fin.zero_le i))
  have hk_gt : x ⟨0, by omega⟩ > y ⟨0, by omega⟩ := by
    simp [x, y, Matrix.cons_val_zero]
  -- y' = y (agrees with y on i ≤ 0, i.e., i = 0)
  have hy'_eq : ∀ i : Fin 2, i ≤ ⟨0, by omega⟩ → y i = y i := fun _ _ => rfl
  have hnca := hNCA x y ⟨0, by omega⟩ hk_eq hk_gt y hy'_eq
  -- Show QPROT_strict y x
  have hyx : y ≠ x := by
    intro h; have := congr_fun h ⟨0, by omega⟩; simp [x, y, Matrix.cons_val_zero] at this
  have h3_dt : (3 : ℝ) ∈ differingThresholds y x := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and]
      exact Or.inl ⟨⟨1, by omega⟩, by simp [y, Matrix.cons_val_one, Matrix.head_cons]⟩
    · intro heq
      have h1y : (⟨1, by omega⟩ : Fin 2) ∈ coverageSet y 3 := by
        rw [mem_coverageSet]; simp [y, Matrix.cons_val_one, Matrix.head_cons]
      rw [heq, mem_coverageSet] at h1y
      have : x (⟨1, by omega⟩ : Fin 2) = (0 : ℝ) := by
        simp [x, Matrix.cons_val_one, Matrix.head_cons]
      linarith
  have hqprot : QPROT_strict y x := qprot_strict_of_data 3 h3_dt
    (by
      intro b hb
      rw [differingThresholds, Finset.mem_filter] at hb; obtain ⟨hb_tv, _⟩ := hb
      simp only [thresholdValues, mem_union, mem_image, mem_univ, true_and] at hb_tv
      rcases hb_tv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> fin_cases i <;>
        simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons] <;> norm_num)
    ⟨1, by omega⟩
    (by
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet]; left; constructor
      · simp [y, Matrix.cons_val_one, Matrix.head_cons]
      · simp [x, Matrix.cons_val_one, Matrix.head_cons])
    (by
      intro ⟨s, hs⟩ hmem
      simp only [coverageSymmDiff, mem_symmDiff, mem_coverageSet,
        Fin.le_iff_val_le_val] at hmem ⊢
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> interval_cases s <;>
        simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons] at h1 h2 ⊢ <;> linarith)
    (by rw [mem_coverageSet]; simp [y, Matrix.cons_val_one, Matrix.head_cons])
  exact hnca (QPROT_strictPart_of_strict hyx hqprot)
