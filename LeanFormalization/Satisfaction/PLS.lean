/-
  PriorityRanking.Satisfaction.PLS
  Which axioms PLS satisfies and violates.

  Satisfies: C, T, PD, NCA, TSM, UPT, CST, CX
  Violates: TSI, TM, TI, GUT, CVG, LTSF, HTSF, EI
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms
import LeanFormalization.Characterizations.PLS

/-! ## PLS satisfies: C, T, PD, NCA (already proven in Characterizations/PLS.lean) -/

-- PLS_satisfies_C, PLS_satisfies_T, PLS_satisfies_PD, PLS_satisfies_NCA
-- are exported from LeanFormalization.Characterizations.PLS

/-! ## PLS satisfies UPT -/

/-- PLS satisfies Upward Priority Transfer: transferring δ > 0 from state k+1 to state k
    gives a strict improvement, because x_k = y_k + δ > y_k at the first differing index. -/
theorem PLS_satisfies_UPT {n : ℕ} : Ax_UPT (@PLS n) := by
  intro x y k δ hδ hk hxk _hxk1 hother _hnn
  constructor
  · -- PLS x y: first differing index is ≤ k, and x wins there
    right
    refine ⟨k, fun j hj => ?_, ?_⟩
    · -- For j < k: x j = y j (from hother, j ≠ k and j ≠ k+1 since j < k)
      have hj_ne_k : j ≠ k := ne_of_lt hj
      have hj_ne_k1 : j.val ≠ k.val + 1 := by omega
      exact (hother j hj_ne_k hj_ne_k1).symm
    · -- y k < x k: since x_k = y_k + δ and δ > 0
      linarith
  · -- ¬PLS y x
    intro hyx
    rcases hyx with rfl | ⟨j, hj_eq, hj_lt⟩
    · -- y = x: but x k = y k + δ with δ > 0, contradiction
      linarith
    · -- PLS_strict y x at j: x j < y j, and ∀ i < j, x i = y i
      -- If j ≤ k: x j = y j (for j < k by hother) or j = k and x k > y k. Either way, ¬(x j < y j).
      -- If j > k: x j = y j (hother for j ≠ k, j ≠ k+1) unless j = k+1.
      by_cases hjk : j ≤ k
      · rcases eq_or_lt_of_le hjk with rfl | hlt
        · -- j = k: x k < y k? But x k = y k + δ > y k. Contradiction.
          linarith
        · -- j < k: x j = y j (hother). But hj_lt says x j < y j. Contradiction.
          have hj_ne_k : j ≠ k := ne_of_lt hlt
          have hj_ne_k1 : j.val ≠ k.val + 1 := by omega
          linarith [hother j hj_ne_k hj_ne_k1]
      · -- j > k: hj_eq at k gives x k = y k, but x k = y k + δ > y k. Contradiction.
        push_neg at hjk
        have := hj_eq k hjk
        linarith

/-! ## PLS violates TM -/

/-- PLS violates Total Monotonicity: (2,0) has lower total than (0,3), but PLS ranks (2,0) first. -/
theorem PLS_violates_TM : ¬ Ax_TM (@PLS 2) := by
  intro hTM
  let x : Vec 2 := ![0, 3]
  let y : Vec 2 := ![2, 0]
  -- totalSum x = 3 > 2 = totalSum y
  have htotal : totalSum x > totalSum y := by
    simp only [totalSum]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    norm_num
  have hstrict := hTM x y htotal
  -- hstrict : strictPart PLS x y, i.e., PLS x y ∧ ¬PLS y x
  -- But PLS y x because y₀ = 2 > 0 = x₀
  have hyx : PLS y x := Or.inr ⟨⟨0, by omega⟩,
    fun j hj => absurd hj (not_lt.mpr (Fin.zero_le j)),
    by simp [x, y, Matrix.cons_val_zero]⟩
  exact hstrict.2 hyx

/-! ## PLS violates TI -/

/-- PLS violates Total Indifference: (1,0) and (0,1) have equal totals but PLS is not indifferent. -/
theorem PLS_violates_TI : ¬ Ax_TI (@PLS 2) := by
  intro hTI
  let x : Vec 2 := ![1, 0]
  let y : Vec 2 := ![0, 1]
  have htotal : totalSum x = totalSum y := by
    simp only [totalSum]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hindiff := hTI x y htotal
  -- indiffPart means PLS x y ∧ PLS y x
  -- But PLS x y is strict: x₀ = 1 > 0 = y₀, so ¬PLS y x
  have hyx_false : ¬ PLS y x := by
    intro hyx
    rcases hyx with heq | ⟨k, hk_eq, hk_lt⟩
    · have := congr_fun heq ⟨0, by omega⟩
      simp [x, y, Matrix.cons_val_zero] at this
    · -- hk_lt: x k < y k, hk_eq: ∀ j < k, x j = y j
      -- If k = 0: x 0 < y 0, i.e., 1 < 0, contradiction
      -- If k = 1: hk_eq at 0 gives x 0 = y 0, i.e., 1 = 0, contradiction
      fin_cases k
      · simp [x, y, Matrix.cons_val_zero] at hk_lt; linarith
      · have := hk_eq ⟨0, by omega⟩ (by simp [Fin.lt_def])
        simp [x, y, Matrix.cons_val_zero] at this
  exact hyx_false hindiff.2

/-! ## PLS satisfies TSM -/

/-- PLS satisfies Top-State Monotonicity: if x₀ > y₀, then x ≻_PLS y (first diff is at index 0). -/
theorem PLS_satisfies_TSM {n : ℕ} [NeZero n] : Ax_TSM (@PLS n) := by
  intro x y hgt
  constructor
  · -- PLS x y: strict at index 0
    right
    exact ⟨⟨0, NeZero.pos n⟩,
      fun j hj => absurd hj (not_lt.mpr (Fin.zero_le j)),
      by linarith⟩
  · -- ¬PLS y x
    intro hyx
    rcases hyx with rfl | ⟨k, hk_eq, hk_lt⟩
    · linarith
    · by_cases hk0 : k.val = 0
      · have : k = ⟨0, NeZero.pos n⟩ := Fin.ext hk0
        rw [this] at hk_lt; linarith
      · have : (⟨0, NeZero.pos n⟩ : Fin n) < k := by
          simp only [Fin.lt_def]; omega
        linarith [hk_eq ⟨0, NeZero.pos n⟩ this]

/-! ## PLS violates TSI -/

/-- PLS violates Top-State Indifference: (1,2) and (1,0) have equal x₀ but PLS is not indifferent. -/
theorem PLS_violates_TSI : ¬ Ax_TSI (@PLS 2) := by
  intro hTSI
  let x : Vec 2 := ![1, 2]
  let y : Vec 2 := ![1, 0]
  have htop : x ⟨0, by omega⟩ = y ⟨0, by omega⟩ := by
    simp [x, y, Matrix.cons_val_zero]
  have hindiff := hTSI x y htop
  -- PLS y x would require y ≻_PLS x or y = x
  -- But PLS_strict x y since x₁ = 2 > 0 = y₁ (first diff at index 1)
  have hyx_false : ¬ PLS y x := by
    intro hyx
    rcases hyx with heq | ⟨k, hk_eq, hk_lt⟩
    · have := congr_fun heq ⟨1, by omega⟩
      simp [x, y, Matrix.cons_val_one, Matrix.head_cons] at this
    · -- hk_lt: x k < y k
      fin_cases k
      · simp [x, y, Matrix.cons_val_zero] at hk_lt
      · simp [x, y, Matrix.cons_val_one, Matrix.head_cons] at hk_lt; linarith
  exact hyx_false hindiff.2

/-! ## PLS violates GUT -/

/-- PLS violates Generalized Upward Transfer: x = (0,5,0), y = (2,0,3) have equal totals
    with x₂ < y₂, but PLS ranks y above x since y₀ = 2 > 0 = x₀. -/
theorem PLS_violates_GUT : ¬ Ax_GUT (@PLS 3) := by
  intro hGUT
  let x : Vec 3 := ![0, 5, 0]
  let y : Vec 3 := ![2, 0, 3]
  -- k = ⟨1, _⟩, so k+1 = 2
  have htotal : totalSum x = totalSum y := by
    simp only [totalSum]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hstrict : strictPart PLS x y := by
    have hk1 : (1 : ℕ) + 1 < 3 := by omega
    have hagree : ∀ i : Fin 3, i.val > 1 + 1 → x i = y i := by
      intro ⟨i, hi⟩ hgt; exfalso; omega
    have hlt : x ⟨1 + 1, hk1⟩ < y ⟨1 + 1, hk1⟩ := by
      simp [x, y, Matrix.cons_val_one]
    exact hGUT x y ⟨1, by omega⟩ hk1 hagree hlt htotal
  -- But PLS y x since y₀ = 2 > 0 = x₀
  have hyx : PLS y x := Or.inr ⟨⟨0, by omega⟩,
    fun j hj => absurd hj (not_lt.mpr (Fin.zero_le j)),
    by simp [x, y, Matrix.cons_val_zero]⟩
  exact hstrict.2 hyx

/-! ## PLS satisfies CST -/

/-- PLS satisfies Coordinate Sure-Thing: the ranking depends only on non-common coordinates.
    If x, y agree on S and x', y' agree on S, and x = x', y = y' outside S,
    then PLS x y ↔ PLS x' y'. -/
theorem PLS_satisfies_CST {n : ℕ} : Ax_CST (@PLS n) := by
  intro S x y x' y' hS_xy hS_x'y' hnotS_x hnotS_y
  -- Key fact: coordinate differences are preserved
  have hdiff : ∀ j : Fin n, x j - y j = x' j - y' j := by
    intro j
    by_cases hj : j ∈ S
    · linarith [hS_xy j hj, hS_x'y' j hj]
    · linarith [hnotS_x j hj, hnotS_y j hj]
  simp only [PLS]
  constructor
  · intro hxy
    rcases hxy with rfl | ⟨k, hk_eq, hk_lt⟩
    · -- x = y → x' = y'
      left; funext j; linarith [hdiff j]
    · -- PLS_strict x y → PLS_strict x' y' (same first-diff index, same direction)
      right; exact ⟨k, fun j hj => by linarith [hdiff j, hk_eq j hj],
        by linarith [hdiff k]⟩
  · intro hxy
    rcases hxy with rfl | ⟨k, hk_eq, hk_lt⟩
    · left; funext j; linarith [hdiff j]
    · right; exact ⟨k, fun j hj => by linarith [hdiff j, hk_eq j hj],
        by linarith [hdiff k]⟩

/-! ## PLS satisfies CX -/

/-- PLS satisfies Convexity: upper contour sets are convex.
    If PLS x z and PLS y z, then PLS (λx + (1-λ)y) z for 0 < λ < 1.
    At the first index where z and the combo differ, the combo wins because it's
    a positive combination of values that weakly/strictly exceed z. -/
theorem PLS_satisfies_CX {n : ℕ} : Ax_CX (@PLS n) := by
  intro x y z lam hxz hyz hlam0 hlam1
  have h1lam : 0 < 1 - lam := by linarith
  -- After rfl from PLS x z: z is removed, x survives
  -- After rfl from PLS y z: z is removed, y survives (or x if z was already removed)
  -- PLS_strict a b = Pi.Lex (· < ·) (· < ·) b a, so equality is b j = a j
  rcases hxz with rfl | ⟨k₁, hk₁_eq, hk₁_lt⟩
  · -- x = z → z removed, x survives. hyz : PLS y x
    rcases hyz with rfl | ⟨k₂, hk₂_eq, hk₂_lt⟩
    · -- y = x: combo = x
      left; funext i; ring
    · -- PLS_strict y x at k₂: hk₂_eq : ∀ j < k₂, x j = y j, hk₂_lt : x k₂ < y k₂
      -- Goal: PLS combo x. PLS_strict combo x has eq: x j = combo j
      right; refine ⟨k₂, fun j hj => ?_, ?_⟩
      · change x j = lam * x j + (1 - lam) * y j
        rw [← (hk₂_eq j hj)]; ring
      · change x k₂ < lam * x k₂ + (1 - lam) * y k₂
        nlinarith
  · -- PLS_strict x z at k₁: hk₁_eq : ∀ j < k₁, z j = x j, hk₁_lt : z k₁ < x k₁
    rcases hyz with rfl | ⟨k₂, hk₂_eq, hk₂_lt⟩
    · -- y = z → z removed, y survives. hk₁_eq now : ∀ j < k₁, y j = x j
      -- Goal: PLS combo y. PLS_strict combo y has eq: y j = combo j
      right; refine ⟨k₁, fun j hj => ?_, ?_⟩
      · change y j = lam * x j + (1 - lam) * y j
        rw [(hk₁_eq j hj)]; ring
      · change y k₁ < lam * x k₁ + (1 - lam) * y k₁
        nlinarith
    · -- Both strict: x, y, z all in scope
      -- hk₁_eq : ∀ j < k₁, z j = x j, hk₂_eq : ∀ j < k₂, z j = y j
      -- Goal: PLS combo z. PLS_strict combo z has eq: z j = combo j
      right
      by_cases h : k₁ ≤ k₂
      · refine ⟨k₁, fun j hj => ?_, ?_⟩
        · change z j = lam * x j + (1 - lam) * y j
          rw [← (hk₁_eq j hj), ← (hk₂_eq j (lt_of_lt_of_le hj h))]; ring
        · change z k₁ < lam * x k₁ + (1 - lam) * y k₁
          rcases eq_or_lt_of_le h with rfl | hlt
          · nlinarith  -- both strict at same index
          · nlinarith [hk₂_eq k₁ hlt]  -- z k₁ = y k₁
      · push_neg at h
        refine ⟨k₂, fun j hj => ?_, ?_⟩
        · change z j = lam * x j + (1 - lam) * y j
          rw [← (hk₁_eq j (lt_trans hj h)), ← (hk₂_eq j hj)]; ring
        · change z k₂ < lam * x k₂ + (1 - lam) * y k₂
          nlinarith [hk₁_eq k₂ h]

/-! ## PLS violates EI -/

/-- PLS violates Equitable Invariance: swapping coordinates of (1,0) gives (0,1),
    but PLS strictly prefers (1,0). -/
theorem PLS_violates_EI : ¬ Ax_EI (@PLS 2) := by
  intro hEI
  let x : Vec 2 := ![1, 0]
  let xπ : Vec 2 := ![0, 1]
  -- Construct the swap permutation and prove x ∘ π = xπ
  have ⟨π, hcomp⟩ : ∃ π : Equiv.Perm (Fin 2), x ∘ ⇑π = xπ := by
    refine ⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩, ?_⟩
    funext ⟨i, hi⟩; interval_cases i
    · change x (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩) = xπ ⟨0, by omega⟩
      rw [Equiv.swap_apply_left]
      simp [x, xπ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · change x (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨1, by omega⟩) = xπ ⟨1, by omega⟩
      rw [Equiv.swap_apply_right]
      simp [x, xπ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hindiff := hEI x π
  rw [hcomp] at hindiff
  have : ¬ PLS xπ x := by
    intro h
    rcases h with heq | ⟨k, hk_eq, hk_lt⟩
    · have := congr_fun heq ⟨0, by omega⟩
      simp [x, xπ, Matrix.cons_val_zero] at this
    · fin_cases k
      · simp [x, xπ, Matrix.cons_val_zero] at hk_lt; linarith
      · have := hk_eq ⟨0, by omega⟩ (by simp [Fin.lt_def])
        simp [x, xπ, Matrix.cons_val_zero] at this
  exact this hindiff.2
