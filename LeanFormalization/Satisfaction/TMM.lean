/-
  PriorityRanking.Satisfaction.TMM
  Which axioms TMM satisfies and violates.

  Satisfies: C, T, PD, TM, TI, CST, CX, EI
  Violates: TSM, TSI, NCA, GUT, NUTC, NDTC
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms
import LeanFormalization.Satisfaction.Witnesses

/-! ## TMM satisfies: C, T, TM, TI -/

theorem TMM_satisfies_C {n : ℕ} : Ax_C (@TMM n) := by
  intro x y
  simp only [TMM, ge_iff_le]
  exact le_total (totalSum y) (totalSum x)

theorem TMM_satisfies_T {n : ℕ} : Ax_T (@TMM n) := by
  intro x y z hxy hyz
  simp only [TMM, ge_iff_le] at *
  exact le_trans hyz hxy

theorem TMM_satisfies_TM' {n : ℕ} : Ax_TM (@TMM n) := by
  intro x y hgt
  simp only [strictPart, TMM, ge_iff_le, not_le]
  exact ⟨le_of_lt hgt, hgt⟩

theorem TMM_satisfies_TI' {n : ℕ} : Ax_TI (@TMM n) := by
  intro x y heq
  simp only [indiffPart, TMM, ge_iff_le]
  exact ⟨le_of_eq heq.symm, le_of_eq heq⟩

/-! ## TMM satisfies PD -/

theorem TMM_satisfies_PD {n : ℕ} : Ax_PD (@TMM n) := by
  intro x y hge hstrict
  simp only [strictPart, TMM, ge_iff_le, not_le, totalSum]
  obtain ⟨j, hj⟩ := hstrict
  exact ⟨Finset.sum_le_sum (fun i _ => hge i),
         Finset.sum_lt_sum (fun i _ => hge i) ⟨j, Finset.mem_univ j, hj⟩⟩

/-! ## TMM satisfies CST -/

theorem TMM_satisfies_CST {n : ℕ} : Ax_CST (@TMM n) := by
  intro S x y x' y' hS_xy hS_x'y' hnotS_x hnotS_y
  simp only [TMM, ge_iff_le, totalSum]
  -- The total-sum comparison only depends on coordinate differences.
  -- On S: x = y and x' = y', so differences are 0.
  -- Off S: x = x' and y = y', so differences are preserved.
  suffices h : ∑ i, x i - ∑ i, y i = ∑ i, x' i - ∑ i, y' i by
    constructor
    · intro hle; linarith
    · intro hle; linarith
  have hdiff : ∀ i, x i - y i = x' i - y' i := by
    intro i
    by_cases hi : i ∈ S
    · have := hS_xy i hi; have := hS_x'y' i hi; linarith
    · have := hnotS_x i hi; have := hnotS_y i hi; linarith
  have : ∑ i : Fin n, x i - ∑ i, y i = ∑ i, x' i - ∑ i, y' i := by
    have h1 : ∑ i : Fin n, (x i - y i) = ∑ i, (x' i - y' i) :=
      Finset.sum_congr rfl (fun i _ => hdiff i)
    linarith [Finset.sum_sub_distrib (f := x) (g := y) (s := Finset.univ),
              Finset.sum_sub_distrib (f := x') (g := y') (s := Finset.univ)]
  linarith

/-! ## TMM satisfies CX -/

theorem TMM_satisfies_CX {n : ℕ} : Ax_CX (@TMM n) := by
  intro x y z lam hxz hyz hlam0 hlam1
  simp only [TMM, ge_iff_le, totalSum] at *
  have h1 : 0 ≤ 1 - lam := by linarith
  -- ∑ (lam * x_i + (1-lam) * y_i) = lam * ∑ x_i + (1-lam) * ∑ y_i
  have hconv : ∑ i : Fin n, (lam * x i + (1 - lam) * y i) =
      lam * ∑ i, x i + (1 - lam) * ∑ i, y i := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  linarith [hconv, mul_le_mul_of_nonneg_left hxz (le_of_lt hlam0),
            mul_le_mul_of_nonneg_left hyz h1]

/-! ## TMM satisfies EI -/

theorem TMM_satisfies_EI {n : ℕ} : Ax_EI (@TMM n) := by
  intro x π
  simp only [indiffPart, TMM, ge_iff_le, totalSum, Function.comp]
  have heq : ∑ i : Fin n, x (π i) = ∑ i, x i :=
    Finset.sum_equiv π (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩)
      (fun _ _ => rfl)
  constructor <;> linarith

/-! ## TMM violates TSM -/

theorem TMM_violates_TSM : ¬ Ax_TSM (@TMM 2) := by
  intro hTSM
  let x : Vec 2 := ![2, 0]
  let y : Vec 2 := ![1, 100]
  have hgt : x ⟨0, by omega⟩ > y ⟨0, by omega⟩ := by
    simp [x, y, Matrix.cons_val_zero]
  have hstrict : strictPart TMM x y := hTSM x y hgt
  simp only [strictPart, TMM, ge_iff_le, not_le, totalSum] at hstrict
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at hstrict
  simp only [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hstrict
  linarith [hstrict.1]

/-! ## TMM violates TSI -/

/-- TMM violates Top-State Indifference: x=(1,2) and y=(1,0) share the top
    coordinate, but TMM strictly prefers x (total 3 > 1). -/
theorem TMM_violates_TSI : ¬ Ax_TSI (@TMM 2) := by
  intro hTSI
  let x : Vec 2 := ![1, 2]
  let y : Vec 2 := ![1, 0]
  have htop : x ⟨0, by omega⟩ = y ⟨0, by omega⟩ := by
    simp [x, y, Matrix.cons_val_zero]
  have hindiff := hTSI x y htop
  have h2 := hindiff.2  -- TMM y x : totalSum y ≥ totalSum x, i.e., 1 ≥ 3
  simp only [TMM, ge_iff_le] at h2
  have htx : totalSum x = 3 := by
    simp only [totalSum]; rw [Fin.sum_univ_two]
    norm_num [x, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hty : totalSum y = 1 := by
    simp only [totalSum]; rw [Fin.sum_univ_two]
    norm_num [y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  linarith

/-! ## TMM violates NCA -/

/-- TMM violates NCA: with x=(1,0), y=(0,0), the first differing coordinate
    favors x, so NCA forbids any y' agreeing with y up to that coordinate from
    beating x — yet y'=(0,5) beats x on totals. -/
theorem TMM_violates_NCA : ¬ Ax_NCA (@TMM 2) := by
  intro hNCA
  let x : Vec 2 := ![1, 0]
  let y : Vec 2 := ![0, 0]
  let y' : Vec 2 := ![0, 5]
  have hk_eq : ∀ i : Fin 2, i < ⟨0, by omega⟩ → x i = y i := by
    intro i hi; exact absurd hi (not_lt.mpr (Fin.zero_le i))
  have hk_gt : x ⟨0, by omega⟩ > y ⟨0, by omega⟩ := by
    norm_num [x, y, Matrix.cons_val_zero]
  have hy' : ∀ i : Fin 2, i ≤ ⟨0, by omega⟩ → y' i = y i := by
    intro i hi
    have h0 : i = ⟨0, by omega⟩ := le_antisymm hi (Fin.zero_le i)
    rw [h0]; simp [y', y, Matrix.cons_val_zero]
  have hforbid := hNCA x y ⟨0, by omega⟩ hk_eq hk_gt y' hy'
  apply hforbid
  rw [TMM_strict]
  simp only [totalSum]; rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [x, y', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-! ## TMM violates GUT -/

/-- TMM violates Generalized Upward Transfer: x=(2,0) and y=(1,1) have equal
    totals with x₁ < y₁, so GUT demands x ≻ y, but TMM is indifferent. -/
theorem TMM_violates_GUT : ¬ Ax_GUT (@TMM 2) := by
  intro hGUT
  let x : Vec 2 := ![2, 0]
  let y : Vec 2 := ![1, 1]
  have htotal : totalSum x = totalSum y := by
    simp only [totalSum]; rw [Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hk1 : (0 : ℕ) + 1 < 2 := by omega
  have hagree : ∀ i : Fin 2, i.val > 0 + 1 → x i = y i := by
    intro ⟨i, hi⟩ hgt; exfalso; omega
  have hlt : x ⟨0 + 1, hk1⟩ < y ⟨0 + 1, hk1⟩ := by
    simp [x, y, Matrix.cons_val_one]
  have hstrict := hGUT x y ⟨0, by omega⟩ hk1 hagree hlt htotal
  apply hstrict.2
  show TMM y x
  simp only [TMM, ge_iff_le]
  linarith [htotal]

/-! ## TMM violates NUTC -/

/-- TMM violates NUTC: P-PROT strictly prefers (1,1) to (3,0), so NUTC forbids
    ranking (3,0) strictly above (1,1) — but TMM does exactly that (3 > 2). -/
theorem TMM_violates_NUTC : ¬ Ax_NUTC (@TMM 2) := by
  intro h
  have hxy : (![1, 1] : Vec 2) ≠ ![3, 0] := by
    intro heq; have := congr_fun heq ⟨0, by omega⟩
    norm_num [Matrix.cons_val_zero] at this
  refine not_strict_of_NUTC h hxy pprot_strict_11_30 ((TMM_strict _ _).mpr ?_)
  simp only [totalSum]; rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-! ## TMM violates NDTC -/

/-- TMM violates NDTC: Q-PROT strictly prefers (3,0) to (2,2), so NDTC forbids
    ranking (2,2) strictly above (3,0) — but TMM does exactly that (4 > 3). -/
theorem TMM_violates_NDTC : ¬ Ax_NDTC (@TMM 2) := by
  intro h
  have hxy : (![3, 0] : Vec 2) ≠ ![2, 2] := by
    intro heq; have := congr_fun heq ⟨0, by omega⟩
    norm_num [Matrix.cons_val_zero] at this
  refine not_strict_of_NDTC h hxy qprot_strict_30_22 ((TMM_strict _ _).mpr ?_)
  simp only [totalSum]; rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
