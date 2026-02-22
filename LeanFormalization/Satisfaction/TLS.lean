/-
  PriorityRanking.Satisfaction.TLS
  Which axioms TLS satisfies and violates.

  Satisfies: C, T, PD, TM, UPT, GUT, CST, CX
  Violates: TSM, TSI, TI, NCA, CVG, LTSF, HTSF, EI
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms
import LeanFormalization.Characterizations.TLS
import LeanFormalization.Structural.Refinement

/-! ## TLS satisfies: C, TM, GUT (already proven in Characterizations/TLS.lean) -/

-- TLS_satisfies_C, TLS_satisfies_TM, TLS_satisfies_GUT
-- are exported from LeanFormalization.Characterizations.TLS

/-! ## TLS satisfies T -/

/-- TLS satisfies Transitivity. -/
theorem TLS_satisfies_T {n : ℕ} : Ax_T (@TLS n) := by
  intro x y z hxy hyz
  rcases hxy with rfl | ⟨k₁, hk₁_eq, hk₁_lt⟩
  · exact hyz
  · rcases hyz with rfl | ⟨k₂, hk₂_eq, hk₂_lt⟩
    · exact Or.inr ⟨k₁, hk₁_eq, hk₁_lt⟩
    · right
      rcases lt_trichotomy k₁ k₂ with h | rfl | h
      · -- k₁ < k₂: use k₂ as witness
        refine ⟨k₂, fun j hj => ?_, ?_⟩
        · linarith [hk₂_eq j hj, hk₁_eq j (lt_trans h hj)]
        · linarith [hk₁_eq k₂ h]
      · -- k₁ = k₂: same index, direct transitivity
        refine ⟨k₁, fun j hj => ?_, ?_⟩
        · linarith [hk₁_eq j hj, hk₂_eq j hj]
        · linarith
      · -- k₁ > k₂: use k₁ as witness
        refine ⟨k₁, fun j hj => ?_, ?_⟩
        · linarith [hk₁_eq j hj, hk₂_eq j (lt_trans h hj)]
        · linarith [hk₂_eq k₁ h]

/-! ## TLS satisfies PD -/

/-- TLS satisfies Pareto Dominance. -/
theorem TLS_satisfies_PD {n : ℕ} [NeZero n] : Ax_PD (@TLS n) := by
  intro x y hge hstrict
  obtain ⟨j, hj⟩ := hstrict
  constructor
  · -- TLS x y via TMM_strict_imp_TLS_strict
    right
    exact TMM_strict_imp_TLS_strict x y (by
      simp only [totalSum]
      exact Finset.sum_lt_sum (fun i _ => hge i) ⟨j, Finset.mem_univ j, hj⟩)
  · -- ¬TLS y x: all prefix sums of x ≥ those of y
    intro hyx
    rcases hyx with rfl | ⟨k, hk_eq, hk_lt⟩
    · linarith
    · simp only [prefixVec] at hk_lt
      have : prefixSum x k ≥ prefixSum y k := by
        simp only [prefixSum]
        exact Finset.sum_le_sum (fun i _ => hge i)
      linarith

/-! ## TLS satisfies UPT -/

/-- TLS satisfies Upward Priority Transfer.
    Proof sketch: the transfer from k+1 to k creates S_k(x) = S_k(y) + δ (strict at k)
    while cancelling for j > k (S_j(x) = S_j(y)). -/
theorem TLS_satisfies_UPT {n : ℕ} : Ax_UPT (@TLS n) := by
  intro x y k δ hδ hk hxk hxk1 hother _hnn
  -- Step 1: prefix sums agree for j < k (coords below k agree)
  have hcoord_below : ∀ i : Fin n, i < k → x i = y i := by
    intro i hi
    have hi_ne_k : i ≠ k := ne_of_lt hi
    have hi_ne_k1 : i.val ≠ k.val + 1 := by
      intro h
      have : k.val < i.val := by omega
      exact absurd (show k < i from this) (not_lt.mpr hi.le)
    exact hother i hi_ne_k hi_ne_k1
  have hps_below : ∀ j : Fin n, j < k → prefixSum x j = prefixSum y j := by
    intro j hj
    exact prefixSum_eq_of_coord_eq x y j (fun i hi => hcoord_below i (lt_of_le_of_lt hi hj))
  -- Step 2: prefixSum x k = prefixSum y k + δ
  have hps_k : prefixSum x k = prefixSum y k + δ := by
    by_cases hk_zero : k.val = 0
    · have hk0 : k = ⟨0, by omega⟩ := Fin.ext hk_zero
      rw [hk0, prefixSum_zero x (by omega), prefixSum_zero y (by omega)]
      rw [hk0] at hxk; linarith
    · have hk_pred_lt : k.val - 1 < n := by omega
      have hsx := prefixSum_succ x (k.val - 1) (by omega) hk_pred_lt
      have hsy := prefixSum_succ y (k.val - 1) (by omega) hk_pred_lt
      have hk_eq_fin : (⟨(k.val - 1) + 1, by omega⟩ : Fin n) = k :=
        Fin.ext (show (k.val - 1) + 1 = k.val by omega)
      rw [hk_eq_fin] at hsx hsy
      have hprev := hps_below ⟨k.val - 1, hk_pred_lt⟩
        (show (⟨k.val - 1, hk_pred_lt⟩ : Fin n) < k from by
          show k.val - 1 < k.val; omega)
      linarith
  -- Step 3: prefixSum x (k+1) = prefixSum y (k+1) (δ and -δ cancel)
  have hps_k1 : prefixSum x ⟨k.val + 1, hk⟩ = prefixSum y ⟨k.val + 1, hk⟩ := by
    have hsx := prefixSum_succ x k.val hk k.isLt
    have hsy := prefixSum_succ y k.val hk k.isLt
    have hk_eq_fin : (⟨k.val, k.isLt⟩ : Fin n) = k := Fin.ext rfl
    rw [hk_eq_fin] at hsx hsy
    linarith
  -- Step 4: prefix sums agree for j > k (combining step 3 with coord agreement above k+1)
  have hps_above : ∀ j : Fin n, j > k → prefixSum x j = prefixSum y j := by
    intro ⟨j, hj_lt⟩ hj
    change k.val < j at hj
    induction j with
    | zero => omega
    | succ m ih =>
      by_cases hm_eq : m = k.val
      · -- m = k.val, so j = k.val + 1
        have hm1_eq : m + 1 = k.val + 1 := by omega
        have : (⟨m + 1, hj_lt⟩ : Fin n) = ⟨k.val + 1, hk⟩ := Fin.ext hm1_eq
        rw [this]; exact hps_k1
      · -- m > k.val
        have hm_gt : k.val < m := by omega
        have hm_lt_n : m < n := by omega
        have ih_m := ih hm_lt_n hm_gt
        have hsx := prefixSum_succ x m hj_lt hm_lt_n
        have hsy := prefixSum_succ y m hj_lt hm_lt_n
        have hcoord_eq : x ⟨m + 1, hj_lt⟩ = y ⟨m + 1, hj_lt⟩ := by
          have hne_k : (⟨m + 1, hj_lt⟩ : Fin n) ≠ k := by
            intro h; simp [Fin.ext_iff] at h; omega
          have hne_k1 : (m + 1) ≠ k.val + 1 := by omega
          exact hother ⟨m + 1, hj_lt⟩ hne_k hne_k1
        have hm_eq_fin : (⟨m, hm_lt_n⟩ : Fin n) = ⟨m, hm_lt_n⟩ := rfl
        linarith
  -- Step 5: TLS x y via TLS_strict with witness k
  constructor
  · right
    refine ⟨k, fun j hj => ?_, ?_⟩
    · simp only [prefixVec]
      exact (hps_above j hj).symm
    · simp only [prefixVec]
      linarith
  -- Step 6: ¬TLS y x
  · intro hyx
    rcases hyx with rfl | ⟨k', hk'_above, hk'_lt⟩
    · linarith
    · simp only [prefixVec] at hk'_above hk'_lt
      by_cases hk'_gt : k' > k
      · -- k' > k: prefix sums agree above k, contradiction with hk'_lt
        linarith [hps_above k' hk'_gt]
      · push_neg at hk'_gt
        rcases eq_or_lt_of_le hk'_gt with rfl | hlt
        · -- k' = k: prefixSum y k < prefixSum x k, but we showed the opposite
          linarith
        · -- k' < k: hk'_above at k gives prefixSum y k = prefixSum x k, contradiction
          linarith [hk'_above k hlt]

/-! ## TLS satisfies CST -/

/-- TLS satisfies Coordinate Sure-Thing. -/
theorem TLS_satisfies_CST {n : ℕ} : Ax_CST (@TLS n) := by
  intro S x y x' y' hS_xy hS_x'y' hnotS_x hnotS_y
  have hdiff : ∀ j : Fin n, x j - y j = x' j - y' j := by
    intro j
    by_cases hj : j ∈ S
    · linarith [hS_xy j hj, hS_x'y' j hj]
    · linarith [hnotS_x j hj, hnotS_y j hj]
  have hpsdiff : ∀ j : Fin n, prefixSum x j - prefixSum y j =
      prefixSum x' j - prefixSum y' j := by
    intro j
    simp only [prefixSum]
    linarith [Finset.sum_sub_distrib (f := x) (g := y) (s := Finset.Iic j),
              Finset.sum_sub_distrib (f := x') (g := y') (s := Finset.Iic j),
              Finset.sum_congr (show Finset.Iic j = Finset.Iic j from rfl)
                (show ∀ i ∈ Finset.Iic j, x i - y i = x' i - y' i from
                  fun i _ => hdiff i)]
  simp only [TLS]
  constructor
  · intro hxy
    rcases hxy with rfl | ⟨k, hk_eq, hk_lt⟩
    · left; funext j; linarith [hdiff j]
    · right; refine ⟨k, fun j hj => ?_, ?_⟩
      · simp only [prefixVec] at hk_eq ⊢; linarith [hpsdiff j, hk_eq j hj]
      · simp only [prefixVec] at hk_lt ⊢; linarith [hpsdiff k]
  · intro hxy
    rcases hxy with rfl | ⟨k, hk_eq, hk_lt⟩
    · left; funext j; linarith [hdiff j]
    · right; refine ⟨k, fun j hj => ?_, ?_⟩
      · simp only [prefixVec] at hk_eq ⊢; linarith [hpsdiff j, hk_eq j hj]
      · simp only [prefixVec] at hk_lt ⊢; linarith [hpsdiff k]

/-! ## TLS satisfies CX -/

/-- TLS satisfies Convexity: upper contour sets are convex.
    Uses linearity of prefix sums and the same convex combination argument as PLS CX,
    but with the reverse-index lexicographic order (witness is max, not min). -/
theorem TLS_satisfies_CX {n : ℕ} : Ax_CX (@TLS n) := by
  intro x y z lam hxz hyz hlam0 hlam1
  have h1lam : 0 < 1 - lam := by linarith
  -- Key: prefix sums are linear in the input vector
  have hps_lin : ∀ j : Fin n,
      prefixSum (fun i => lam * x i + (1 - lam) * y i) j =
      lam * prefixSum x j + (1 - lam) * prefixSum y j := by
    intro j; simp only [prefixSum, Finset.sum_add_distrib, ← Finset.mul_sum]
  rcases hxz with rfl | ⟨k₁, hk₁_eq, hk₁_lt⟩
  · -- x = z → z removed, x survives. hyz : TLS y x
    rcases hyz with rfl | ⟨k₂, hk₂_eq, hk₂_lt⟩
    · -- y = x: combo = x
      left; funext i; ring
    · -- TLS_strict y x at k₂
      -- hk₂_eq : ∀ j > k₂, prefixVec x j = prefixVec y j
      -- hk₂_lt : prefixVec x k₂ < prefixVec y k₂
      right; refine ⟨k₂, fun j hj => ?_, ?_⟩
      · simp only [prefixVec] at hk₂_eq ⊢
        change prefixSum x j = prefixSum (fun i => lam * x i + (1 - lam) * y i) j
        rw [hps_lin, ← (hk₂_eq j hj)]; ring
      · simp only [prefixVec] at hk₂_lt ⊢
        change prefixSum x k₂ < prefixSum (fun i => lam * x i + (1 - lam) * y i) k₂
        rw [hps_lin]; nlinarith
  · -- TLS_strict x z at k₁
    -- hk₁_eq : ∀ j > k₁, prefixVec z j = prefixVec x j
    -- hk₁_lt : prefixVec z k₁ < prefixVec x k₁
    rcases hyz with rfl | ⟨k₂, hk₂_eq, hk₂_lt⟩
    · -- y = z → z removed, y survives
      right; refine ⟨k₁, fun j hj => ?_, ?_⟩
      · simp only [prefixVec] at hk₁_eq ⊢
        change prefixSum y j = prefixSum (fun i => lam * x i + (1 - lam) * y i) j
        rw [hps_lin, (hk₁_eq j hj)]; ring
      · simp only [prefixVec] at hk₁_lt ⊢
        change prefixSum y k₁ < prefixSum (fun i => lam * x i + (1 - lam) * y i) k₁
        rw [hps_lin]; nlinarith
    · -- Both strict: witness is max(k₁, k₂)
      right
      simp only [prefixVec] at hk₁_eq hk₁_lt hk₂_eq hk₂_lt
      by_cases h : k₂ ≤ k₁
      · -- k₁ ≥ k₂: witness is k₁
        refine ⟨k₁, fun j hj => ?_, ?_⟩
        · simp only [prefixVec]
          change prefixSum z j = prefixSum (fun i => lam * x i + (1 - lam) * y i) j
          rw [hps_lin, ← (hk₁_eq j hj), ← (hk₂_eq j (lt_of_le_of_lt h hj))]; ring
        · simp only [prefixVec]
          change prefixSum z k₁ < prefixSum (fun i => lam * x i + (1 - lam) * y i) k₁
          rw [hps_lin]
          rcases eq_or_lt_of_le h with rfl | hlt
          · nlinarith  -- both strict at same index
          · nlinarith [hk₂_eq k₁ hlt]  -- prefixSum z k₁ = prefixSum y k₁
      · -- k₂ > k₁: witness is k₂
        push_neg at h
        refine ⟨k₂, fun j hj => ?_, ?_⟩
        · simp only [prefixVec]
          change prefixSum z j = prefixSum (fun i => lam * x i + (1 - lam) * y i) j
          rw [hps_lin, ← (hk₁_eq j (lt_trans h hj)), ← (hk₂_eq j hj)]; ring
        · simp only [prefixVec]
          change prefixSum z k₂ < prefixSum (fun i => lam * x i + (1 - lam) * y i) k₂
          rw [hps_lin]
          nlinarith [hk₁_eq k₂ h]

/-! ## Helper: compute prefix sum at last index for Fin 2 -/

private theorem prefixSum_last_eq_totalSum_fin2 (x : Vec 2) :
    prefixSum x ⟨1, by omega⟩ = totalSum x := by
  rw [totalSum_eq_prefixSum_last x]

/-! ## TLS violates TSM -/

/-- TLS violates TSM: (2,0) has higher x₀ than (1,100), but TLS ranks (1,100) first. -/
theorem TLS_violates_TSM : ¬ Ax_TSM (@TLS 2) := by
  intro hTSM
  let x : Vec 2 := ![2, 0]
  let y : Vec 2 := ![1, 100]
  have hgt : x ⟨0, by omega⟩ > y ⟨0, by omega⟩ := by
    simp [x, y, Matrix.cons_val_zero]
  have hstrict := hTSM x y hgt
  -- TLS y x via higher total
  have hyx : TLS y x := by
    right; exact TMM_strict_imp_TLS_strict y x (by
      simp only [totalSum]; rw [Fin.sum_univ_two, Fin.sum_univ_two]
      simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num)
  exact hstrict.2 hyx

/-! ## TLS violates TI -/

/-- TLS violates Total Indifference: (1,0) and (0,1) have equal totals but TLS is not indifferent. -/
theorem TLS_violates_TI : ¬ Ax_TI (@TLS 2) := by
  intro hTI
  let x : Vec 2 := ![1, 0]
  let y : Vec 2 := ![0, 1]
  have htotal : totalSum x = totalSum y := by
    simp only [totalSum]; rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hindiff := hTI x y htotal
  have hyx_false : ¬ TLS y x := by
    intro hyx
    rcases hyx with heq | ⟨k, hk_eq, hk_lt⟩
    · have := congr_fun heq ⟨0, by omega⟩
      simp [x, y, Matrix.cons_val_zero] at this
    · simp only [prefixVec] at hk_eq hk_lt
      fin_cases k
      · -- k = 0: S₀(x) < S₀(y)? i.e., 1 < 0. No.
        rw [prefixSum_zero x (by omega), prefixSum_zero y (by omega)] at hk_lt
        simp [x, y, Matrix.cons_val_zero] at hk_lt; linarith
      · -- k = 1: S₁(x) < S₁(y)? Equal totals, so no.
        rw [prefixSum_last_eq_totalSum_fin2, prefixSum_last_eq_totalSum_fin2] at hk_lt
        linarith
  exact hyx_false hindiff.2

/-! ## TLS violates TSI -/

/-- TLS violates TSI: (0,1) and (0,0) have equal x₀ but TLS is not indifferent. -/
theorem TLS_violates_TSI : ¬ Ax_TSI (@TLS 2) := by
  intro hTSI
  let x : Vec 2 := ![0, 1]
  let y : Vec 2 := ![0, 0]
  have htop : x ⟨0, by omega⟩ = y ⟨0, by omega⟩ := by
    simp [x, y, Matrix.cons_val_zero]
  have hindiff := hTSI x y htop
  have hyx_false : ¬ TLS y x := by
    intro hyx
    rcases hyx with heq | ⟨k, hk_eq, hk_lt⟩
    · have := congr_fun heq ⟨1, by omega⟩
      simp [x, y, Matrix.cons_val_one, Matrix.head_cons] at this
    · simp only [prefixVec] at hk_lt
      fin_cases k
      · rw [prefixSum_zero x (by omega), prefixSum_zero y (by omega)] at hk_lt
        simp [x, y, Matrix.cons_val_zero] at hk_lt
      · rw [prefixSum_last_eq_totalSum_fin2, prefixSum_last_eq_totalSum_fin2] at hk_lt
        simp only [totalSum] at hk_lt
        rw [Fin.sum_univ_two, Fin.sum_univ_two] at hk_lt
        simp [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hk_lt
        linarith
  exact hyx_false hindiff.2

/-! ## TLS violates NCA -/

/-- TLS violates NCA: x = (2,0), y = (1,0), y' = (1,100). x₀ > y₀ but TLS ranks y' above x. -/
theorem TLS_violates_NCA : ¬ Ax_NCA (@TLS 2) := by
  intro hNCA
  let x : Vec 2 := ![2, 0]
  let y : Vec 2 := ![1, 0]
  let y' : Vec 2 := ![1, 100]
  have hvac : ∀ i : Fin 2, i < ⟨0, by omega⟩ → x i = y i := by
    intro i hi; exact absurd hi (not_lt.mpr (Fin.zero_le i))
  have hxk : x ⟨0, by omega⟩ > y ⟨0, by omega⟩ := by
    simp [x, y, Matrix.cons_val_zero]
  have hy' : ∀ i : Fin 2, i ≤ ⟨0, by omega⟩ → y' i = y i := by
    intro i hi
    have hi0 : i = ⟨0, by omega⟩ := le_antisymm hi (Fin.zero_le i)
    rw [hi0]; simp [y', y, Matrix.cons_val_zero]
  have hNCA_inst := hNCA x y ⟨0, by omega⟩ hvac hxk y' hy'
  apply hNCA_inst
  constructor
  · -- TLS y' x: y' has much higher total
    right; exact TMM_strict_imp_TLS_strict y' x (by
      simp only [totalSum]; rw [Fin.sum_univ_two, Fin.sum_univ_two]
      simp [x, y', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; norm_num)
  · -- ¬TLS x y'
    intro hxy'
    rcases hxy' with heq | ⟨k, hk_eq, hk_lt⟩
    · have := congr_fun heq ⟨1, by omega⟩
      simp [x, y', Matrix.cons_val_one, Matrix.head_cons] at this
    · simp only [prefixVec] at hk_eq hk_lt
      fin_cases k
      · -- k = 0: hk_eq at j=1 gives S₁(y') = S₁(x), i.e., 101 = 2
        have h1 := hk_eq ⟨1, by omega⟩ (by simp [Fin.lt_def])
        rw [prefixSum_last_eq_totalSum_fin2, prefixSum_last_eq_totalSum_fin2] at h1
        simp only [totalSum] at h1; rw [Fin.sum_univ_two, Fin.sum_univ_two] at h1
        simp [x, y', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h1
        linarith
      · rw [prefixSum_last_eq_totalSum_fin2, prefixSum_last_eq_totalSum_fin2] at hk_lt
        simp only [totalSum] at hk_lt
        rw [Fin.sum_univ_two, Fin.sum_univ_two] at hk_lt
        simp [x, y', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hk_lt
        linarith

/-! ## TLS violates EI -/

/-- TLS violates Equitable Invariance: (1,0) and (0,1) have the same coordinates
    but different prefix sums, so TLS strictly prefers (1,0). -/
theorem TLS_violates_EI : ¬ Ax_EI (@TLS 2) := by
  intro hEI
  let x : Vec 2 := ![1, 0]
  let xπ : Vec 2 := ![0, 1]
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
  -- TLS strictly prefers x over xπ: S₀(x) = 1 > 0 = S₀(xπ), equal totals
  have : ¬ TLS xπ x := by
    intro h
    rcases h with heq | ⟨k, hk_eq, hk_lt⟩
    · have := congr_fun heq ⟨0, by omega⟩
      simp [x, xπ, Matrix.cons_val_zero] at this
    · simp only [prefixVec] at hk_eq hk_lt
      fin_cases k
      · -- k = 0: hk_eq at 1 gives S₁(x) = S₁(xπ) (both = 1), then hk_lt: S₀(x) < S₀(xπ)
        -- S₀(x) = 1, S₀(xπ) = 0, so 1 < 0, contradiction
        rw [prefixSum_zero x (by omega), prefixSum_zero xπ (by omega)] at hk_lt
        simp [x, xπ, Matrix.cons_val_zero] at hk_lt; linarith
      · -- k = 1: hk_lt says S₁(x) < S₁(xπ), but totals are equal
        rw [prefixSum_last_eq_totalSum_fin2, prefixSum_last_eq_totalSum_fin2] at hk_lt
        simp only [totalSum] at hk_lt
        rw [Fin.sum_univ_two, Fin.sum_univ_two] at hk_lt
        simp [x, xπ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hk_lt
  exact this hindiff.2
