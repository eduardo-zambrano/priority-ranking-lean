/-
  PriorityRanking.Characterizations.TLS
  Theorem 4: TLS = C + TM + GUT.

  TLS is characterized by exactly three axioms:
  Completeness, Total Monotonicity, and Generalized Upward Transfer.
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms

open Finset

/-! ## Helper lemmas -/

private theorem ne_imp_prefixSum_ne {n : ℕ} (x y : Vec n) (hne : x ≠ y) :
    ∃ j : Fin n, prefixSum x j ≠ prefixSum y j := by
  by_contra h; push_neg at h; exact hne (eq_of_prefixSum_eq x y h)

/-- No Fin n element is greater than ⟨n-1, _⟩. -/
private theorem Fin.not_gt_last {n : ℕ} (hn : 0 < n) (j : Fin n) :
    ¬ (j > (⟨n - 1, by omega⟩ : Fin n)) := by
  simp only [Fin.lt_def, Fin.val_mk]; omega

/-- Prefix sums agree above k when coords agree above k+1 and totals agree.
    Uses: totalSum x = totalSum y, and ∀ i > k+1, x i = y i.
    Proves: ∀ j > k, prefixSum x j = prefixSum y j. -/
private theorem prefixSum_eq_above_of_coord_eq {n : ℕ} (x y : Vec n) (k : Fin n)
    (hk1 : k.val + 1 < n)
    (hcoord : ∀ i : Fin n, i.val > k.val + 1 → x i = y i)
    (htotal : totalSum x = totalSum y) :
    ∀ j : Fin n, j > k → prefixSum x j = prefixSum y j := by
  -- Strategy: S_j(x) = totalSum x - ∑_{i > j} x_i
  -- For j > k, all i > j have i > k+1, so x_i = y_i
  -- Therefore the "tail sum" is the same, and so is the prefix sum
  intro j hj
  have hj_val : j.val > k.val := by exact hj
  -- prefixSum x j = ∑ i ∈ Iic j, x i
  -- totalSum x = ∑ i, x i = ∑ i ∈ Iic j, x i + ∑ i ∈ univ \ Iic j, x i
  have hx_split : totalSum x = prefixSum x j + ∑ i ∈ univ \ Iic j, x i := by
    simp only [totalSum, prefixSum]
    linarith [Finset.sum_sdiff (Finset.subset_univ (Iic j)) (f := x)]
  have hy_split : totalSum y = prefixSum y j + ∑ i ∈ univ \ Iic j, y i := by
    simp only [totalSum, prefixSum]
    linarith [Finset.sum_sdiff (Finset.subset_univ (Iic j)) (f := y)]
  -- For i ∈ univ \ Iic j: i > j > k, so i > k+1 (since j ≥ k+1), hence x i = y i
  have htail : ∑ i ∈ univ \ Iic j, x i = ∑ i ∈ univ \ Iic j, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    apply hcoord
    simp only [mem_sdiff, mem_univ, mem_Iic, true_and, not_le] at hi
    omega
  linarith

/-- If prefix sums agree for j > k, then coords agree for i > k+1. -/
private theorem coord_eq_of_prefixSum_eq_above {n : ℕ} (x y : Vec n)
    (k : ℕ) (hk1 : k + 1 < n)
    (habove : ∀ j : Fin n, j.val > k → prefixSum x j = prefixSum y j) :
    ∀ i : Fin n, i.val > k + 1 → x i = y i := by
  intro ⟨i, hi_lt⟩ hi
  change i > k + 1 at hi
  have hps_i := habove ⟨i, hi_lt⟩ (show i > k by omega)
  have hps_i1 := habove ⟨i - 1, by omega⟩ (show i - 1 > k by omega)
  have hsx := prefixSum_succ x (i - 1) (by omega) (by omega)
  have hsy := prefixSum_succ y (i - 1) (by omega) (by omega)
  have h_eq : (⟨(i - 1) + 1, by omega⟩ : Fin n) = ⟨i, hi_lt⟩ :=
    Fin.ext (show (i - 1) + 1 = i by omega)
  rw [h_eq] at hsx hsy
  linarith

/-! ## Forward direction: TLS satisfies C, TM, GUT -/

theorem TLS_satisfies_C {n : ℕ} : Ax_C (@TLS n) := by
  intro x y
  by_cases heq : x = y
  · exact Or.inl (Or.inl heq)
  · have ⟨j, hj⟩ := ne_imp_prefixSum_ne x y heq
    let K := Finset.univ.filter (fun j : Fin n => prefixSum x j ≠ prefixSum y j)
    have hK : K.Nonempty := ⟨j, by simp [K]; exact hj⟩
    let km := K.max' hK
    have hkm_ne : prefixSum x km ≠ prefixSum y km := by
      have := Finset.max'_mem K hK; simp [K] at this; exact this
    have hkm_max : ∀ j' : Fin n, prefixSum x j' ≠ prefixSum y j' → j' ≤ km :=
      fun j' hj' => Finset.le_max' K j' (by simp [K]; exact hj')
    have habove : ∀ j' : Fin n, j' > km → prefixSum y j' = prefixSum x j' := by
      intro j' hj'; by_contra h'
      exact absurd hj' (not_lt.mpr (hkm_max j' (Ne.symm h')))
    rcases lt_or_gt_of_ne hkm_ne with hlt | hgt
    · exact Or.inr (Or.inr ⟨km,
        fun j' hj' => by simp only [prefixVec]; exact (habove j' hj').symm,
        by simp only [prefixVec]; exact hlt⟩)
    · exact Or.inl (Or.inr ⟨km,
        fun j' hj' => by simp only [prefixVec]; exact habove j' hj',
        by simp only [prefixVec]; exact hgt⟩)

theorem TLS_satisfies_TM {n : ℕ} [NeZero n] : Ax_TM (@TLS n) := by
  intro x y hgt
  have hn := NeZero.pos n
  constructor
  · -- TLS x y: use k = last index (vacuously above, strict at last)
    right
    refine ⟨⟨n - 1, by omega⟩, ?_, ?_⟩
    · intro j hj; exact absurd hj (Fin.not_gt_last hn j)
    · show prefixVec y ⟨n - 1, _⟩ < prefixVec x ⟨n - 1, _⟩
      simp only [prefixVec]
      rw [show totalSum x = prefixSum x ⟨n - 1, by omega⟩ from totalSum_eq_prefixSum_last x,
          show totalSum y = prefixSum y ⟨n - 1, by omega⟩ from totalSum_eq_prefixSum_last y]
        at hgt
      exact hgt
  · -- ¬TLS y x
    intro hyx
    rcases hyx with rfl | ⟨k, hk_above, hk_lt⟩
    · linarith
    · simp only [prefixVec] at hk_above hk_lt
      -- Either k = last (contradiction) or k < last (get prefixSum eq at last → contradiction)
      by_cases hk_last : k = ⟨n - 1, by omega⟩
      · subst hk_last
        rw [show totalSum x = prefixSum x ⟨n - 1, by omega⟩ from totalSum_eq_prefixSum_last x,
            show totalSum y = prefixSum y ⟨n - 1, by omega⟩ from totalSum_eq_prefixSum_last y]
          at hgt
        linarith
      · have hk_ne_val : k.val ≠ n - 1 := by
          intro h; exact hk_last (Fin.ext h)
        have hk_lt_last : k < ⟨n - 1, by omega⟩ :=
          show k.val < n - 1 by omega
        have := hk_above ⟨n - 1, by omega⟩ hk_lt_last
        rw [show totalSum x = prefixSum x ⟨n - 1, by omega⟩ from totalSum_eq_prefixSum_last x,
            show totalSum y = prefixSum y ⟨n - 1, by omega⟩ from totalSum_eq_prefixSum_last y]
          at hgt
        linarith

theorem TLS_satisfies_GUT {n : ℕ} : Ax_GUT (@TLS n) := by
  intro x y k hk1 hcoord_eq hxk1_lt htotal_eq
  -- Prefix sums agree above k
  have hprefixEq : ∀ j : Fin n, j > k → prefixSum x j = prefixSum y j :=
    prefixSum_eq_above_of_coord_eq x y k hk1 hcoord_eq htotal_eq
  -- S_k(x) > S_k(y)
  have hprefixLt : prefixSum x k > prefixSum y k := by
    have h_eq := hprefixEq ⟨k.val + 1, hk1⟩ (show k.val < k.val + 1 by omega)
    have hsx := prefixSum_succ x k.val hk1 k.isLt
    have hsy := prefixSum_succ y k.val hk1 k.isLt
    have hk_eq : (⟨k.val, k.isLt⟩ : Fin n) = k := Fin.ext rfl
    rw [hk_eq] at hsx hsy
    linarith
  constructor
  · right
    exact ⟨k,
      fun j hj => by simp only [prefixVec]; exact (hprefixEq j hj).symm,
      by simp only [prefixVec]; exact hprefixLt⟩
  · intro hyx
    rcases hyx with rfl | ⟨k', hk'_above, hk'_lt⟩
    · exact absurd hxk1_lt (not_lt.mpr le_rfl)
    · simp only [prefixVec] at hk'_above hk'_lt
      by_cases hk'_gt : k' > k
      · linarith [hprefixEq k' hk'_gt]
      · push_neg at hk'_gt
        rcases eq_or_lt_of_le hk'_gt with rfl | hlt
        · linarith
        · linarith [hk'_above k hlt]

/-! ## Reverse direction: C + TM + GUT implies TLS -/

private theorem tls_strict_imp_strict {n : ℕ} [NeZero n] {R : PrefRel n}
    (hTM : Ax_TM R) (hGUT : Ax_GUT R)
    (x y : Vec n) (h : TLS_strict x y) : strictPart R x y := by
  obtain ⟨k, hk_above, hk_lt⟩ := h
  simp only [prefixVec] at hk_above hk_lt
  have hn := NeZero.pos n
  by_cases hk_last : k = ⟨n - 1, by omega⟩
  · -- Case 1: TM
    apply hTM
    rw [show totalSum x = prefixSum x ⟨n - 1, by omega⟩ from totalSum_eq_prefixSum_last x,
        show totalSum y = prefixSum y ⟨n - 1, by omega⟩ from totalSum_eq_prefixSum_last y]
    subst hk_last; exact hk_lt
  · -- Case 2: GUT
    have hk_ne_val : k.val ≠ n - 1 := fun h => hk_last (Fin.ext h)
    have hk_lt_last : k.val + 1 ≤ n - 1 := by omega
    have hk1 : k.val + 1 < n := by omega
    have habove_k1 : prefixSum x ⟨k.val + 1, hk1⟩ = prefixSum y ⟨k.val + 1, hk1⟩ :=
      (hk_above ⟨k.val + 1, hk1⟩ (show k.val < k.val + 1 by omega)).symm
    have htotal : totalSum x = totalSum y := by
      rw [show totalSum x = prefixSum x ⟨n - 1, by omega⟩ from totalSum_eq_prefixSum_last x,
          show totalSum y = prefixSum y ⟨n - 1, by omega⟩ from totalSum_eq_prefixSum_last y]
      exact (hk_above ⟨n - 1, by omega⟩ (show k.val < n - 1 by omega)).symm
    have hcoord : ∀ i : Fin n, i.val > k.val + 1 → x i = y i :=
      coord_eq_of_prefixSum_eq_above x y k.val hk1
        (fun j hj => (hk_above j hj).symm)
    have hxk1 : x ⟨k.val + 1, hk1⟩ < y ⟨k.val + 1, hk1⟩ := by
      have hsx := prefixSum_succ x k.val hk1 k.isLt
      have hsy := prefixSum_succ y k.val hk1 k.isLt
      have hk_eq : (⟨k.val, k.isLt⟩ : Fin n) = k := Fin.ext rfl
      rw [hk_eq] at hsx hsy
      linarith
    exact hGUT x y k hk1 hcoord hxk1 htotal

theorem C_TM_GUT_imp_TLS {n : ℕ} [NeZero n] {R : PrefRel n}
    (hC : Ax_C R) (hTM : Ax_TM R) (hGUT : Ax_GUT R) :
    ∀ x y, R x y ↔ TLS x y := by
  intro x y
  constructor
  · intro hRxy
    by_cases heq : x = y
    · exact Or.inl heq
    · rcases TLS_satisfies_C x y with hxy | hyx
      · exact hxy
      · rcases hyx with rfl | hyx_strict
        · exact Or.inl rfl
        · exfalso
          exact (tls_strict_imp_strict hTM hGUT y x hyx_strict).2 hRxy
  · intro hTLS
    rcases hTLS with rfl | hstrict
    · rcases hC x x with h | h <;> exact h
    · exact (tls_strict_imp_strict hTM hGUT x y hstrict).1

/-! ## Main characterization -/

theorem TLS_characterization {n : ℕ} [NeZero n] {R : PrefRel n} :
    (∀ x y, R x y ↔ TLS x y) ↔ (Ax_C R ∧ Ax_TM R ∧ Ax_GUT R) := by
  constructor
  · intro hR
    refine ⟨?_, ?_, ?_⟩
    · intro x y
      rcases TLS_satisfies_C x y with h | h
      · exact Or.inl ((hR x y).mpr h)
      · exact Or.inr ((hR y x).mpr h)
    · intro x y hgt
      have h := TLS_satisfies_TM x y hgt
      exact ⟨(hR x y).mpr h.1, fun hR' => h.2 ((hR y x).mp hR')⟩
    · intro x y k hk1 hcoord hxk1 htotal
      have h := TLS_satisfies_GUT x y k hk1 hcoord hxk1 htotal
      exact ⟨(hR x y).mpr h.1, fun hR' => h.2 ((hR y x).mp hR')⟩
  · rintro ⟨hC, hTM, hGUT⟩
    exact C_TM_GUT_imp_TLS hC hTM hGUT
