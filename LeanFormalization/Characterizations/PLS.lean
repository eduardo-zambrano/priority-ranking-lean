/-
  PriorityRanking.Characterizations.PLS
  Theorem 2: PLS = C + T + PD + NCA.

  PLS is characterized by exactly four axioms:
  Completeness, Transitivity, Pareto Dominance, and Non-Compensability.
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms

open Finset

/-! ## Helper: first differing index -/

/-- For x ≠ y, the minimum index where they differ. -/
private noncomputable def firstDiff {n : ℕ} (x y : Vec n) (hne : x ≠ y) : Fin n :=
  let S := Finset.univ.filter (fun i : Fin n => x i ≠ y i)
  have hS : S.Nonempty := by
    rw [Finset.filter_nonempty_iff]
    by_contra h; push_neg at h
    exact hne (funext (fun i => by simpa using h i (Finset.mem_univ i)))
  S.min' hS

private theorem firstDiff_ne {n : ℕ} (x y : Vec n) (hne : x ≠ y) :
    x (firstDiff x y hne) ≠ y (firstDiff x y hne) := by
  have hS : (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).Nonempty := by
    rw [Finset.filter_nonempty_iff]
    by_contra h; push_neg at h
    exact hne (funext (fun i => by simpa using h i (Finset.mem_univ i)))
  exact Finset.mem_filter.mp (Finset.min'_mem _ hS) |>.2

private theorem firstDiff_eq_below {n : ℕ} (x y : Vec n) (hne : x ≠ y) :
    ∀ i : Fin n, i < firstDiff x y hne → x i = y i := by
  intro i hi
  by_contra h
  have hi_mem : i ∈ Finset.univ.filter (fun j : Fin n => x j ≠ y j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
  have hS : (Finset.univ.filter (fun j : Fin n => x j ≠ y j)).Nonempty := ⟨i, hi_mem⟩
  exact absurd (Finset.min'_le _ i hi_mem) (not_le.mpr hi)

/-! ## Forward direction: PLS satisfies C, T, PD, NCA -/

theorem PLS_satisfies_C {n : ℕ} : Ax_C (@PLS n) := by
  intro x y
  by_cases heq : x = y
  · exact Or.inl (Or.inl heq)
  · -- Find first differing index
    have hne_yx : y ≠ x := fun h => heq (h.symm)
    rcases lt_or_gt_of_ne (firstDiff_ne x y heq) with hlt | hgt
    · -- x k < y k: PLS y x (Pi.Lex x y needs x j = y j)
      right; right
      exact ⟨firstDiff x y heq,
        fun j hj => firstDiff_eq_below x y heq j hj,
        hlt⟩
    · -- x k > y k: PLS x y (Pi.Lex y x needs y j = x j)
      left; right
      exact ⟨firstDiff x y heq,
        fun j hj => (firstDiff_eq_below x y heq j hj).symm,
        hgt⟩

theorem PLS_satisfies_T {n : ℕ} : Ax_T (@PLS n) := by
  intro x y z hxy hyz
  rcases hxy with rfl | ⟨k₁, hk₁_eq, hk₁_lt⟩
  · exact hyz
  · rcases hyz with rfl | ⟨k₂, hk₂_eq, hk₂_lt⟩
    · exact Or.inr ⟨k₁, hk₁_eq, hk₁_lt⟩
    · -- Both PLS_strict: k₁ is first diff of (x,y), k₂ is first diff of (y,z)
      -- For j < min(k₁,k₂): x j = y j = z j
      -- At min(k₁,k₂): x > z
      right
      rcases lt_trichotomy k₁ k₂ with h | h | h
      · -- k₁ < k₂: use k₁
        exact ⟨k₁, fun j hj => by
          have := hk₁_eq j hj
          have := hk₂_eq j (lt_trans hj h)
          linarith,
          by linarith [hk₂_eq k₁ h]⟩
      · -- k₁ = k₂: use k₁
        subst h
        exact ⟨k₁, fun j hj => by linarith [hk₁_eq j hj, hk₂_eq j hj],
          by linarith⟩
      · -- k₂ < k₁: use k₂
        exact ⟨k₂, fun j hj => by
          have := hk₂_eq j hj
          have := hk₁_eq j (lt_trans hj h)
          linarith,
          by linarith [hk₁_eq k₂ h]⟩

theorem PLS_satisfies_PD {n : ℕ} : Ax_PD (@PLS n) := by
  intro x y hge hstrict
  constructor
  · -- R x y
    by_cases heq : x = y
    · -- x = y contradicts hstrict
      obtain ⟨j, hj⟩ := hstrict
      exact absurd (by rw [heq] : x j = y j) (ne_of_gt hj)
    · -- x ≠ y: first differing index k has x k > y k (from ≥ and ≠)
      right
      exact ⟨firstDiff x y heq,
        fun j hj => (firstDiff_eq_below x y heq j hj).symm,
        lt_of_le_of_ne (hge _) (Ne.symm (firstDiff_ne x y heq))⟩
  · -- ¬R y x
    intro hyx
    rcases hyx with rfl | ⟨k, hk_eq, hk_lt⟩
    · obtain ⟨j, hj⟩ := hstrict; linarith [hge j]
    · -- y k > x k, but x k ≥ y k, contradiction
      linarith [hge k]

theorem PLS_satisfies_NCA {n : ℕ} : Ax_NCA (@PLS n) := by
  intro x y k hvac hxk_gt y' hy' hstrict
  -- hstrict : strictPart PLS y' x, i.e., PLS y' x ∧ ¬ PLS x y'
  obtain ⟨hy'x, _⟩ := hstrict
  rcases hy'x with rfl | ⟨j, hj_eq, hj_lt⟩
  · -- y' = x: x k > y k but y' = x, and y' k = y k ≤ x k = y' k, contradiction
    linarith [hy' k (le_refl k)]
  · -- PLS_strict y' x at index j: y' j > x j, and ∀ i < j, x i = y' i
    -- Case 1: j < k. Then x j = y j (from hvac) and y' j = y j (from hy', j ≤ k).
    -- So y' j = y j = x j, contradicting y' j > x j.
    -- Case 2: j = k. Then y' k = y k (from hy') and y' k > x k.
    -- But x k > y k = y' k, contradiction.
    -- Case 3: j > k. Then x j = y' j (from hj_eq), but we need j < k or j = k.
    -- Actually for j > k: x j = y' j from hj_eq? No, hj_eq says ∀ i < j, x i = y' i.
    -- We need: if j ≤ k, contradiction from above. If j > k, then k < j so x k = y' k (from hj_eq).
    -- y' k = y k (from hy'), so x k = y k, contradicting x k > y k.
    by_cases hjk : j ≤ k
    · -- j ≤ k
      rcases lt_or_eq_of_le hjk with hlt | heq_jk
      · -- j < k: x j = y j (from hvac), y' j = y j (from hy'). So x j = y' j.
        -- But hj_lt says x j < y' j. Contradiction.
        linarith [hvac j hlt, hy' j hjk]
      · -- j = k: y' k = y k (from hy'), x k > y k. So x k > y' k.
        -- But hj_lt says x k < y' k (since j = k). Contradiction.
        rw [heq_jk] at hj_lt
        linarith [hy' k (le_refl k)]
    · -- j > k: k < j, so x k = y' k (hj_eq). y' k = y k (hy'). Contradiction.
      push_neg at hjk
      linarith [hj_eq k hjk, hy' k (le_refl k)]

/-! ## Reverse direction: C + T + PD + NCA implies PLS -/

/-- Key lemma: C + T + PD + NCA imply that if x_k > y_k at the first differing
    index k, then x is strictly preferred to y. -/
private theorem axioms_imp_pls_strict {n : ℕ} {R : PrefRel n}
    (hC : Ax_C R) (hT : Ax_T R) (hPD : Ax_PD R) (hNCA : Ax_NCA R)
    (x y : Vec n) (_hne : x ≠ y)
    (k : Fin n) (hvac : ∀ i : Fin n, i < k → x i = y i) (hxk : x k > y k) :
    strictPart R x y := by
  -- Step 1: NCA gives ¬(y ≻ x), hence x ≿ y by Completeness
  have h_not_yx : ¬ strictPart R y x := by
    exact hNCA x y k hvac hxk y (fun i _ => rfl)
  have hRxy : R x y := by
    rcases hC x y with h | h
    · exact h
    · by_contra hnotRxy
      exact h_not_yx ⟨h, hnotRxy⟩
  -- Step 2: Prove strictness by contradiction. Assume x ~ y (indifferent).
  constructor
  · exact hRxy
  · intro hRyx
    -- So R y x holds. We derive a contradiction.
    -- Construct y_ε: agree with y everywhere except at k, where y_ε k = y k + ε
    -- for ε ∈ (0, x k - y k).
    -- Construct y_ε with (y_ε)_k = y_k + ε for ε = (x_k - y_k)/2
    set y_eps : Vec n := fun i => if i = k then y i + (x k - y k) / 2 else y i with hy_eps_def
    -- y_eps Pareto-dominates y
    have hge : ∀ i : Fin n, y_eps i ≥ y i := by
      intro i; simp only [hy_eps_def]
      split <;> linarith
    have hstrict_at_k : y_eps k > y k := by
      simp only [hy_eps_def, if_pos rfl]; linarith
    have hPD_y_eps : strictPart R y_eps y :=
      hPD y_eps y hge ⟨k, hstrict_at_k⟩
    -- y_eps ≻ x: from R y_eps y (PD) + R y x (transitivity), and ¬R x y_eps
    have hR_ye_x : strictPart R y_eps x := by
      exact ⟨hT y_eps y x hPD_y_eps.1 hRyx,
             fun h => hPD_y_eps.2 (hT y x y_eps hRyx h)⟩
    -- NCA contradiction: x and y_eps agree below k, x k > y_eps k
    have hvac' : ∀ i : Fin n, i < k → x i = y_eps i := by
      intro i hi
      simp only [hy_eps_def, if_neg (ne_of_lt hi)]
      exact hvac i hi
    have hxk_gt_ye : x k > y_eps k := by
      simp only [hy_eps_def, if_pos rfl]; linarith
    exact hNCA x y_eps k hvac' hxk_gt_ye y_eps (fun i _ => rfl) hR_ye_x

theorem C_T_PD_NCA_imp_PLS {n : ℕ} {R : PrefRel n}
    (hC : Ax_C R) (hT : Ax_T R) (hPD : Ax_PD R) (hNCA : Ax_NCA R) :
    ∀ x y, R x y ↔ PLS x y := by
  intro x y
  constructor
  · -- R x y → PLS x y
    intro hRxy
    by_cases heq : x = y
    · exact Or.inl heq
    · -- x ≠ y: find first differing index
      rcases lt_or_gt_of_ne (firstDiff_ne x y heq) with hlt | hgt
      · -- x k < y k: PLS says y ≻ x.
        -- By axioms_imp_pls_strict with y, x: y ≻ x, contradicting R x y.
        have hne_yx : y ≠ x := fun h => heq h.symm
        -- Need: first diff from y, x side. Same index k, y k > x k.
        have hvac_yx : ∀ i : Fin n, i < firstDiff x y heq → y i = x i :=
          fun i hi => (firstDiff_eq_below x y heq i hi).symm
        exfalso
        exact (axioms_imp_pls_strict hC hT hPD hNCA y x hne_yx
          (firstDiff x y heq) hvac_yx hlt).2 hRxy
      · -- x k > y k: PLS strict
        exact Or.inr ⟨firstDiff x y heq,
          fun j hj => (firstDiff_eq_below x y heq j hj).symm,
          hgt⟩
  · -- PLS x y → R x y
    intro hPLS
    rcases hPLS with rfl | ⟨k, hk_eq, hk_lt⟩
    · rcases hC x x with h | h <;> exact h
    · exact (axioms_imp_pls_strict hC hT hPD hNCA x y
        (fun h => by rw [h] at hk_lt; linarith)
        k (fun i hi => (hk_eq i hi).symm) (by linarith)).1

/-! ## Main characterization -/

theorem PLS_characterization {n : ℕ} {R : PrefRel n} :
    (∀ x y, R x y ↔ PLS x y) ↔ (Ax_C R ∧ Ax_T R ∧ Ax_PD R ∧ Ax_NCA R) := by
  constructor
  · intro hR
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Completeness
      intro x y
      rcases PLS_satisfies_C x y with h | h
      · exact Or.inl ((hR x y).mpr h)
      · exact Or.inr ((hR y x).mpr h)
    · -- Transitivity
      intro x y z hxy hyz
      exact (hR x z).mpr (PLS_satisfies_T x y z ((hR x y).mp hxy) ((hR y z).mp hyz))
    · -- Pareto Dominance
      intro x y hge hstrict
      have h := PLS_satisfies_PD x y hge hstrict
      exact ⟨(hR x y).mpr h.1, fun hR' => h.2 ((hR y x).mp hR')⟩
    · -- NCA
      intro x y k hvac hxk y' hy'
      intro hstrict
      have hstrict_pls : strictPart PLS y' x :=
        ⟨(hR y' x).mp hstrict.1, fun h => hstrict.2 ((hR x y').mpr h)⟩
      exact PLS_satisfies_NCA x y k hvac hxk y' hy' hstrict_pls
  · rintro ⟨hC, hT, hPD, hNCA⟩
    exact C_T_PD_NCA_imp_PLS hC hT hPD hNCA
