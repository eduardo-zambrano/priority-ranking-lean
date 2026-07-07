/-
  PriorityRanking.Satisfaction.PMM
  Which axioms PMM satisfies and violates.

  Satisfies: C, T, TSM, TSI, NCA, CST, CX
  Violates: PD, TM, TI, GUT, NUTC, NDTC
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms
import LeanFormalization.Satisfaction.Witnesses

/-! ## PMM satisfies: C, T, TSM, TSI -/

theorem PMM_satisfies_C {n : ℕ} [NeZero n] : Ax_C (@PMM n _) := by
  intro x y
  simp only [PMM, ge_iff_le]
  exact le_total (y ⟨0, NeZero.pos n⟩) (x ⟨0, NeZero.pos n⟩)

theorem PMM_satisfies_T {n : ℕ} [NeZero n] : Ax_T (@PMM n _) := by
  intro x y z hxy hyz
  simp only [PMM, ge_iff_le] at *
  exact le_trans hyz hxy

theorem PMM_satisfies_TSM {n : ℕ} [NeZero n] : Ax_TSM (@PMM n _) := by
  intro x y hgt
  simp only [strictPart, PMM, ge_iff_le, not_le]
  exact ⟨le_of_lt hgt, hgt⟩

theorem PMM_satisfies_TSI {n : ℕ} [NeZero n] : Ax_TSI (@PMM n _) := by
  intro x y heq
  simp only [indiffPart, PMM, ge_iff_le]
  exact ⟨le_of_eq heq.symm, le_of_eq heq⟩

/-! ## PMM satisfies NCA -/

/-- PMM satisfies NCA: if x₀ > y₀ (with agreement above 0), no y' with y'₀ = y₀ can beat x. -/
theorem PMM_satisfies_NCA {n : ℕ} [NeZero n] : Ax_NCA (@PMM n _) := by
  intro x y k hvac hgt y' hy'
  -- Need: ¬ strictPart PMM y' x
  -- strictPart PMM y' x means y'₀ > x₀ (from PMM_strict)
  simp only [strictPart, PMM, ge_iff_le, not_le, not_and]
  intro _
  -- Need: ¬(x₀ < y'₀)
  -- Case 1: k = 0. Then x₀ > y₀ and y'₀ = y₀ (from hy' at i = 0, i ≤ k = 0).
  -- So y'₀ = y₀ < x₀, hence ¬(x₀ < y'₀).
  -- Case 2: k > 0. Then x₀ = y₀ (from hvac at i = 0 < k).
  -- And y'₀ = y₀ (from hy' at i = 0 ≤ k). So y'₀ = y₀ = x₀, hence ¬(x₀ < y'₀).
  by_cases hk : (⟨0, NeZero.pos n⟩ : Fin n) < k
  · -- k > 0: x₀ = y₀
    have hx0_eq : x ⟨0, NeZero.pos n⟩ = y ⟨0, NeZero.pos n⟩ := hvac ⟨0, NeZero.pos n⟩ hk
    have hy'0_eq : y' ⟨0, NeZero.pos n⟩ = y ⟨0, NeZero.pos n⟩ :=
      hy' ⟨0, NeZero.pos n⟩ (le_of_lt hk)
    linarith
  · -- k = 0 (since ¬(0 < k) and k : Fin n with k ≥ 0)
    push_neg at hk
    have hk0 : k = ⟨0, NeZero.pos n⟩ := le_antisymm hk (Fin.zero_le k)
    -- y'₀ = y₀ (from hy' at i = 0 ≤ k = 0)
    have hy'0_eq : y' ⟨0, NeZero.pos n⟩ = y ⟨0, NeZero.pos n⟩ :=
      hy' ⟨0, NeZero.pos n⟩ (le_of_eq hk0.symm)
    -- x₀ > y₀ (rewrite hgt using hk0)
    rw [hk0] at hgt
    linarith

/-! ## PMM satisfies CST -/

/-- PMM satisfies CST: ranking depends only on non-common coordinates,
    but PMM only looks at coordinate 0, so if both pairs agree on the replacement
    coordinates and disagree only off those, the ranking is preserved. -/
theorem PMM_satisfies_CST {n : ℕ} [NeZero n] : Ax_CST (@PMM n _) := by
  intro S x y x' y' hS_xy hS_x'y' hnotS_x hnotS_y
  simp only [PMM, ge_iff_le]
  -- Need: x₀ ≥ y₀ ↔ x'₀ ≥ y'₀
  -- Case 1: 0 ∈ S. Then x₀ = y₀ (from hS_xy) and x'₀ = y'₀ (from hS_x'y').
  -- Both ≥ hold. ✓
  -- Case 2: 0 ∉ S. Then x₀ = x'₀ (from hnotS_x) and y₀ = y'₀ (from hnotS_y).
  -- The comparison is the same. ✓
  constructor
  · intro h
    by_cases h0 : ⟨0, NeZero.pos n⟩ ∈ S
    · exact le_of_eq (hS_x'y' _ h0).symm
    · rw [← hnotS_x _ h0, ← hnotS_y _ h0]; exact h
  · intro h
    by_cases h0 : ⟨0, NeZero.pos n⟩ ∈ S
    · exact le_of_eq (hS_xy _ h0).symm
    · rw [hnotS_x _ h0, hnotS_y _ h0]; exact h

/-! ## PMM satisfies CX -/

/-- PMM satisfies CX: upper contour sets are convex (since they're half-spaces
    defined by x₀ ≥ c for some c). -/
theorem PMM_satisfies_CX {n : ℕ} [NeZero n] : Ax_CX (@PMM n _) := by
  intro x y z lam hxz hyz hlam0 hlam1
  simp only [PMM, ge_iff_le] at *
  -- Need: z₀ ≤ λ * x₀ + (1 - λ) * y₀
  -- From hxz: z₀ ≤ x₀, hyz: z₀ ≤ y₀
  -- λ * x₀ + (1-λ) * y₀ ≥ λ * z₀ + (1-λ) * z₀ = z₀
  have h1 : 0 ≤ 1 - lam := by linarith
  calc z ⟨0, NeZero.pos n⟩
      = lam * z ⟨0, NeZero.pos n⟩ + (1 - lam) * z ⟨0, NeZero.pos n⟩ := by ring
    _ ≤ lam * x ⟨0, NeZero.pos n⟩ + (1 - lam) * y ⟨0, NeZero.pos n⟩ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hxz (le_of_lt hlam0)
        · exact mul_le_mul_of_nonneg_left hyz h1

/-! ## PMM violates PD (counterexample) -/

/-- PMM violates PD: (1, 0) Pareto-dominates (1, -1), but PMM is indifferent. -/
theorem PMM_violates_PD : ¬ Ax_PD (@PMM 2 _) := by
  intro hPD
  let x : Vec 2 := ![1, 0]
  let y : Vec 2 := ![1, -1]
  have hge : ∀ i : Fin 2, x i ≥ y i := by
    intro i; fin_cases i <;> simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
  have hstrict : ∃ j : Fin 2, x j > y j :=
    ⟨1, by simp [x, y, Matrix.cons_val_one, Matrix.head_cons]⟩
  have := hPD x y hge hstrict
  simp only [strictPart, PMM, ge_iff_le, not_le] at this
  simp [x, y, Matrix.cons_val_zero] at this

/-! ## PMM violates TM -/

/-- PMM violates Total Monotonicity: x=(0,3) has a higher total than y=(2,0),
    but PMM weakly prefers y (since y₀ = 2 > 0 = x₀). -/
theorem PMM_violates_TM : ¬ Ax_TM (@PMM 2 _) := by
  intro hTM
  let x : Vec 2 := ![0, 3]
  let y : Vec 2 := ![2, 0]
  have htotal : totalSum x > totalSum y := by
    simp only [totalSum]; rw [Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hstrict := hTM x y htotal
  apply hstrict.2
  show PMM y x
  simp only [PMM, ge_iff_le]
  norm_num [x, y, Matrix.cons_val_zero]

/-! ## PMM violates TI -/

/-- PMM violates Total Indifference: x=(2,0) and y=(1,1) have equal totals,
    but PMM strictly prefers x (since x₀ = 2 > 1 = y₀). -/
theorem PMM_violates_TI : ¬ Ax_TI (@PMM 2 _) := by
  intro hTI
  let x : Vec 2 := ![2, 0]
  let y : Vec 2 := ![1, 1]
  have htotal : totalSum x = totalSum y := by
    simp only [totalSum]; rw [Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hindiff := hTI x y htotal
  have h2 := hindiff.2  -- PMM y x : y₀ ≥ x₀, i.e., 1 ≥ 2
  simp only [PMM, ge_iff_le] at h2
  norm_num [x, y, Matrix.cons_val_zero] at h2

/-! ## PMM violates GUT (n = 3) -/

/-- PMM violates Generalized Upward Transfer: x=(1,2,0) and y=(1,0,2) have equal
    totals and equal top coordinates with x₂ < y₂, so GUT demands x ≻ y, but PMM
    is indifferent (x₀ = y₀ = 1). At n = 2 the GUT hypotheses force x₀ > y₀, so
    the minimal counterexample lives at n = 3. -/
theorem PMM_violates_GUT : ¬ Ax_GUT (@PMM 3 _) := by
  intro hGUT
  let x : Vec 3 := ![1, 2, 0]
  let y : Vec 3 := ![1, 0, 2]
  have htotal : totalSum x = totalSum y := by
    simp only [totalSum]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hk1 : (1 : ℕ) + 1 < 3 := by omega
  have hagree : ∀ i : Fin 3, i.val > 1 + 1 → x i = y i := by
    intro ⟨i, hi⟩ hgt; exfalso; omega
  have hlt : x ⟨1 + 1, hk1⟩ < y ⟨1 + 1, hk1⟩ := by
    simp [x, y, Matrix.cons_val_one]
  have hstrict := hGUT x y ⟨1, by omega⟩ hk1 hagree hlt htotal
  apply hstrict.2
  show PMM y x
  simp only [PMM, ge_iff_le]
  norm_num [x, y, Matrix.cons_val_zero]

/-! ## PMM violates NUTC -/

/-- PMM violates NUTC: P-PROT strictly prefers (1,1) to (3,0) (coverage advantage
    at the lowest differing threshold), so NUTC forbids ranking (3,0) strictly
    above (1,1) — but PMM does exactly that (3 > 1 at the top coordinate). -/
theorem PMM_violates_NUTC : ¬ Ax_NUTC (@PMM 2 _) := by
  intro h
  have hxy : (![1, 1] : Vec 2) ≠ ![3, 0] := by
    intro heq; have := congr_fun heq ⟨0, by omega⟩
    norm_num [Matrix.cons_val_zero] at this
  exact not_strict_of_NUTC h hxy pprot_strict_11_30
    ((PMM_strict _ _).mpr (by norm_num [Matrix.cons_val_zero]))

/-! ## PMM violates NDTC -/

/-- PMM violates NDTC: Q-PROT strictly prefers (1,3) to (2,2) (coverage advantage
    at the highest differing threshold), so NDTC forbids ranking (2,2) strictly
    above (1,3) — but PMM does exactly that (2 > 1 at the top coordinate). -/
theorem PMM_violates_NDTC : ¬ Ax_NDTC (@PMM 2 _) := by
  intro h
  have hxy : (![1, 3] : Vec 2) ≠ ![2, 2] := by
    intro heq; have := congr_fun heq ⟨0, by omega⟩
    norm_num [Matrix.cons_val_zero] at this
  exact not_strict_of_NDTC h hxy qprot_strict_13_22
    ((PMM_strict _ _).mpr (by norm_num [Matrix.cons_val_zero]))
