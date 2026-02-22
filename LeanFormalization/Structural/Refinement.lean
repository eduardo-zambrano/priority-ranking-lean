/-
  PriorityRanking.Structural.Refinement
  Structural results: PLS refines PMM, TLS refines TMM, PCL = PLS.
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms

open Finset

/-! ## PLS refines PMM -/

/-- PMM-strict implies PLS-strict: if x₀ > y₀, then PLS ranks x above y. -/
theorem PMM_strict_imp_PLS_strict {n : ℕ} [NeZero n] (x y : Vec n)
    (h : x ⟨0, NeZero.pos n⟩ > y ⟨0, NeZero.pos n⟩) :
    PLS_strict x y :=
  ⟨⟨0, NeZero.pos n⟩,
    fun j hj => absurd hj (not_lt.mpr (Fin.zero_le j)),
    h⟩

/-- PLS refines PMM: strict PMM implies strict PLS. -/
theorem PLS_refines_PMM {n : ℕ} [NeZero n] (x y : Vec n)
    (h : strictPart PMM x y) : strictPart PLS x y := by
  rw [PMM_strict] at h
  exact ⟨Or.inr (PMM_strict_imp_PLS_strict x y h),
    fun hyx => by
      rcases hyx with rfl | ⟨k, hk_eq, hk_lt⟩
      · linarith
      · by_cases hk0 : k.val = 0
        · -- k = 0: hk_lt says x 0 < y 0, contradicts h
          have : k = ⟨0, NeZero.pos n⟩ := Fin.ext hk0
          rw [this] at hk_lt; linarith
        · -- k > 0: hk_eq at 0 gives x 0 = y 0, contradicts h
          have : (⟨0, NeZero.pos n⟩ : Fin n) < k := by
            simp only [Fin.lt_def]; omega
          linarith [hk_eq ⟨0, NeZero.pos n⟩ this]⟩

/-! ## TLS refines TMM -/

/-- TMM-strict implies TLS-strict. -/
theorem TMM_strict_imp_TLS_strict {n : ℕ} [NeZero n] (x y : Vec n)
    (h : totalSum x > totalSum y) :
    TLS_strict x y := by
  have hn := NeZero.pos n
  refine ⟨⟨n - 1, by omega⟩, ?_, ?_⟩
  · intro j hj; exact absurd hj (by simp only [Fin.lt_def, Fin.val_mk]; omega)
  · simp only [prefixVec]
    rw [show totalSum x = prefixSum x ⟨n - 1, by omega⟩ from totalSum_eq_prefixSum_last x,
        show totalSum y = prefixSum y ⟨n - 1, by omega⟩ from totalSum_eq_prefixSum_last y] at h
    exact h

/-- TLS refines TMM: strict TMM implies strict TLS. -/
theorem TLS_refines_TMM {n : ℕ} [NeZero n] (x y : Vec n)
    (h : strictPart TMM x y) : strictPart TLS x y := by
  rw [TMM_strict] at h
  exact ⟨Or.inr (TMM_strict_imp_TLS_strict x y h),
    fun hyx => by
      rcases hyx with rfl | ⟨k, hk_eq, hk_lt⟩
      · linarith
      · simp only [prefixVec] at hk_eq hk_lt
        by_cases hk_last : k.val = n - 1
        · rw [show k = ⟨n - 1, by omega⟩ from Fin.ext hk_last] at hk_lt
          rw [← totalSum_eq_prefixSum_last x, ← totalSum_eq_prefixSum_last y] at hk_lt
          linarith
        · have : k < ⟨n - 1, by omega⟩ := by
            simp only [Fin.lt_def]; omega
          have heq := hk_eq ⟨n - 1, by omega⟩ this
          rw [← totalSum_eq_prefixSum_last x, ← totalSum_eq_prefixSum_last y] at heq
          linarith⟩

/-! ## PCL = PLS -/

/-- Helper: if prefix sums agree below k, then coordinates agree below k. -/
private theorem coord_eq_of_prefixSum_eq_below {n : ℕ} (x y : Vec n)
    (k : Fin n) (h : ∀ j : Fin n, j < k → prefixSum x j = prefixSum y j) :
    ∀ i : Fin n, i < k → x i = y i := by
  intro ⟨i, hi_lt⟩ hi
  change i < k.val at hi
  induction i with
  | zero =>
    have h0 := h ⟨0, by omega⟩ (show (⟨0, by omega⟩ : Fin n).val < k.val by omega)
    rwa [prefixSum_zero x (by omega), prefixSum_zero y (by omega)] at h0
  | succ m ih =>
    have hm_lt_n : m < n := by omega
    have hm1_lt_n : m + 1 < n := hi_lt
    have hps_m1 := h ⟨m + 1, hm1_lt_n⟩ (show m + 1 < k.val by exact hi)
    have hps_m := h ⟨m, hm_lt_n⟩ (show m < k.val by omega)
    have hsx := prefixSum_succ x m hm1_lt_n hm_lt_n
    have hsy := prefixSum_succ y m hm1_lt_n hm_lt_n
    linarith

/-- Helper: if coordinates agree below k, prefix sums agree below k. -/
private theorem prefixSum_eq_of_coord_eq_below {n : ℕ} (x y : Vec n)
    (k : Fin n) (h : ∀ i : Fin n, i < k → x i = y i) :
    ∀ j : Fin n, j < k → prefixSum x j = prefixSum y j := by
  intro j hj
  apply prefixSum_eq_of_coord_eq
  exact fun i hi => h i (lt_of_le_of_lt hi hj)

/-- PLS-strict ↔ lexicographic on prefix sums from index 0 upward. -/
theorem PLS_strict_iff_prefixLex {n : ℕ} (x y : Vec n) :
    PLS_strict x y ↔ Pi.Lex (· < ·) (· < ·) (prefixVec y) (prefixVec x) := by
  constructor
  · -- Forward: PLS_strict → prefix lex
    intro ⟨k, hk_eq, hk_lt⟩
    refine ⟨k, fun j hj => ?_, ?_⟩
    · simp only [prefixVec]
      exact prefixSum_eq_of_coord_eq y x j (fun i hi => hk_eq i (lt_of_le_of_lt hi hj))
    · simp only [prefixVec]
      -- S_k(y) < S_k(x): decompose as S_{k-1} + coord_k
      by_cases hk_zero : k.val = 0
      · have hk0 : k = ⟨0, by omega⟩ := Fin.ext hk_zero
        rw [hk0, prefixSum_zero y (by omega), prefixSum_zero x (by omega)]
        rw [hk0] at hk_lt; exact hk_lt
      · have hk_pred : k.val - 1 < n := by omega
        have hsx := prefixSum_succ x (k.val - 1) (by omega) hk_pred
        have hsy := prefixSum_succ y (k.val - 1) (by omega) hk_pred
        have hk_eq_fin : (⟨(k.val - 1) + 1, by omega⟩ : Fin n) = k :=
          Fin.ext (show (k.val - 1) + 1 = k.val by omega)
        rw [hk_eq_fin] at hsx hsy
        have hprev : prefixSum y ⟨k.val - 1, hk_pred⟩ = prefixSum x ⟨k.val - 1, hk_pred⟩ :=
          prefixSum_eq_of_coord_eq y x ⟨k.val - 1, hk_pred⟩
            (fun i hi => hk_eq i (show i.val < k.val by
              simp only [Fin.le_def] at hi; omega))
        linarith
  · -- Backward: prefix lex → PLS_strict
    intro ⟨k, hk_eq, hk_lt⟩
    simp only [prefixVec] at hk_eq hk_lt
    refine ⟨k, fun j hj => ?_, ?_⟩
    · exact (coord_eq_of_prefixSum_eq_below y x k
        (fun j' hj' => hk_eq j' hj')) j hj
    · -- y k < x k from S_k(y) < S_k(x) and S_{k-1} agreement
      by_cases hk_zero : k.val = 0
      · have hk0 : k = ⟨0, by omega⟩ := Fin.ext hk_zero
        rw [hk0] at hk_lt ⊢
        rw [prefixSum_zero y (by omega), prefixSum_zero x (by omega)] at hk_lt
        exact hk_lt
      · have hk_pred : k.val - 1 < n := by omega
        have hsx := prefixSum_succ x (k.val - 1) (by omega) hk_pred
        have hsy := prefixSum_succ y (k.val - 1) (by omega) hk_pred
        have hk_eq_fin : (⟨(k.val - 1) + 1, by omega⟩ : Fin n) = k :=
          Fin.ext (show (k.val - 1) + 1 = k.val by omega)
        rw [hk_eq_fin] at hsx hsy
        have hprev := hk_eq ⟨k.val - 1, hk_pred⟩
          (show (⟨k.val - 1, hk_pred⟩ : Fin n) < k by
            simp only [Fin.lt_def]; omega)
        linarith

/-- PCL = PLS: lexicographic comparison of prefix sums equals PLS. -/
theorem PCL_eq_PLS {n : ℕ} (x y : Vec n) :
    PLS x y ↔ (x = y ∨ Pi.Lex (· < ·) (· < ·) (prefixVec y) (prefixVec x)) := by
  constructor
  · intro h; rcases h with rfl | hstrict
    · exact Or.inl rfl
    · exact Or.inr ((PLS_strict_iff_prefixLex x y).mp hstrict)
  · intro h; rcases h with rfl | hstrict
    · exact Or.inl rfl
    · exact Or.inr ((PLS_strict_iff_prefixLex x y).mpr hstrict)
