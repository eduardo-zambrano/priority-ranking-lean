/-
  PriorityRanking.Characterizations.PPROT_NUTC
  Theorem: P-PROT = C + T + PD + NUTC.

  P-PROT is characterized by exactly four axioms:
  Completeness, Transitivity, Pareto Dominance, and
  No Upward Threshold Compensation.

  Strategy: leverage the existing C + LTSF characterization.
  1. Show C + LTSF ⟹ C + T + PD + NUTC (easy: PPROT is a weak order, etc.)
  2. Show C + T + PD + NUTC ⟹ R = PPROT (the hard direction)
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms
import LeanFormalization.Characterizations.PPROT

open Finset

/-! ## Forward: P-PROT satisfies T, PD, NUTC -/

/-- Transitivity of P-PROT strict preference via universal threshold sets.
    Given PPROT_strict x y and PPROT_strict y z with x ≠ z, produces PPROT_strict x z.
    Uses enlarged_symmDiff_eq_min to lift verdicts to a common threshold universe,
    then a three-case split (a₁ < a₂, a₁ = a₂, a₁ > a₂), then transfers back. -/
private theorem pprot_strict_trans {n : ℕ} (x y z : Vec n) (hxz : x ≠ z)
    (hxy : PPROT_strict x y) (hyz : PPROT_strict y z) : PPROT_strict x z := by
  obtain ⟨hne_xy, hD_xy, hr_xy⟩ := hxy
  obtain ⟨hne_yz, hD_yz, hr_yz⟩ := hyz
  -- Universal threshold set
  set T := thresholdValues x y ∪ thresholdValues y z
  -- T-level differing thresholds
  set Dxy := T.filter (fun a => coverageSet x a ≠ coverageSet y a)
  set Dyz := T.filter (fun a => coverageSet y a ≠ coverageSet z a)
  set Dxz := T.filter (fun a => coverageSet x a ≠ coverageSet z a)
  -- Subset inclusions
  have hxy_sub : thresholdValues x y ⊆ T := Finset.subset_union_left
  have hyz_sub : thresholdValues y z ⊆ T := Finset.subset_union_right
  have hxz_sub : thresholdValues x z ⊆ T := by
    intro t ht
    rcases Finset.mem_union.mp ht with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr h)))
  -- Coordinate membership in threshold sets
  have hx_xy : ∀ i, x i ∈ thresholdValues x y := fun i =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hy_xy : ∀ i, y i ∈ thresholdValues x y := fun i =>
    Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hy_yz : ∀ i, y i ∈ thresholdValues y z := fun i =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hz_yz : ∀ i, z i ∈ thresholdValues y z := fun i =>
    Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hx_xz : ∀ i, x i ∈ thresholdValues x z := fun i =>
    Finset.mem_union.mpr (Or.inl (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hz_xz : ∀ i, z i ∈ thresholdValues x z := fun i =>
    Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  -- T-level nonemptiness
  have hDxy_ne : Dxy.Nonempty := by
    obtain ⟨a, ha⟩ := hne_xy
    exact ⟨a, Finset.mem_filter.mpr
      ⟨hxy_sub (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩⟩
  have hDyz_ne : Dyz.Nonempty := by
    obtain ⟨a, ha⟩ := hne_yz
    exact ⟨a, Finset.mem_filter.mpr
      ⟨hyz_sub (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩⟩
  -- Lift verdicts from natural threshold sets to T
  have lift_xy := enlarged_symmDiff_eq_min x y _ T hxy_sub hx_xy hy_xy hne_xy hDxy_ne
  have lift_yz := enlarged_symmDiff_eq_min y z _ T hyz_sub hy_yz hz_yz hne_yz hDyz_ne
  -- T-level min thresholds
  set a₁ := Dxy.min' hDxy_ne
  set a₂ := Dyz.min' hDyz_ne
  -- T-level symm diffs are nonempty
  have hSD1_ne : (coverageSymmDiff x y a₁).Nonempty := lift_xy.1 ▸ hD_xy
  have hSD2_ne : (coverageSymmDiff y z a₂).Nonempty := lift_yz.1 ▸ hD_yz
  -- T-level verdicts: min of symm diff ∈ coverage set
  have hv1 : (coverageSymmDiff x y a₁).min' hSD1_ne ∈ coverageSet x a₁ := by
    rw [Finset.min'_of_eq lift_xy.1 hSD1_ne hD_xy, lift_xy.2]; exact hr_xy
  have hv2 : (coverageSymmDiff y z a₂).min' hSD2_ne ∈ coverageSet y a₂ := by
    rw [Finset.min'_of_eq lift_yz.1 hSD2_ne hD_yz, lift_yz.2]; exact hr_yz
  -- Agreement below min differing threshold
  have agree_xy : ∀ t, t ∈ T → t < a₁ → coverageSet x t = coverageSet y t := by
    intro t ht hlt; by_contra h
    exact absurd (Finset.min'_le _ t (Finset.mem_filter.mpr ⟨ht, h⟩)) (not_le.mpr hlt)
  have agree_yz : ∀ t, t ∈ T → t < a₂ → coverageSet y t = coverageSet z t := by
    intro t ht hlt; by_contra h
    exact absurd (Finset.min'_le _ t (Finset.mem_filter.mpr ⟨ht, h⟩)) (not_le.mpr hlt)
  -- T-membership of a₁, a₂
  have ha₁_T : a₁ ∈ T := (Finset.mem_filter.mp (Finset.min'_mem Dxy hDxy_ne)).1
  have ha₂_T : a₂ ∈ T := (Finset.mem_filter.mp (Finset.min'_mem Dyz hDyz_ne)).1
  -- Helper: agreement below both min thresholds
  have no_below : ∀ t, t ∈ T → t < a₁ → t < a₂ → coverageSet x t = coverageSet z t :=
    fun t ht h1 h2 => (agree_xy t ht h1).trans (agree_yz t ht h2)
  -- Helper: show Dxz.min' = a for given a ∈ Dxz, when no Dxz elements below a
  have min_dxz (a : ℝ) (ha : a ∈ Dxz) (hbelow : ∀ t, t ∈ Dxz → a ≤ t) :
      ∃ (hne : Dxz.Nonempty), Dxz.min' hne = a :=
    ⟨⟨a, ha⟩, le_antisymm (Finset.min'_le _ _ ha) (hbelow _ (Finset.min'_mem _ ⟨a, ha⟩))⟩
  -- Helper: no Dxz element below min(a₁, a₂)
  have dxz_lower_bound : ∀ t, t ∈ Dxz → min a₁ a₂ ≤ t := by
    intro t ht
    by_contra hlt; push_neg at hlt
    have ht_T := (Finset.mem_filter.mp ht).1
    exact (Finset.mem_filter.mp ht).2
      (no_below t ht_T (lt_of_lt_of_le hlt (min_le_left _ _))
        (lt_of_lt_of_le hlt (min_le_right _ _)))
  -- Three-case split to establish Dxz verdict at T level
  suffices h : ∃ (hne : Dxz.Nonempty),
      ∃ (hD : (coverageSymmDiff x z (Dxz.min' hne)).Nonempty),
        (coverageSymmDiff x z (Dxz.min' hne)).min' hD ∈ coverageSet x (Dxz.min' hne) by
    -- Transfer from T-level to natural differingThresholds x z
    obtain ⟨hDxz_ne, hSD_ne, hverd⟩ := h
    have hne_xz := differingThresholds_nonempty x z hxz
    have lift_xz := enlarged_symmDiff_eq_min x z _ T hxz_sub hx_xz hz_xz hne_xz hDxz_ne
    -- Natural symm diff = T-level symm diff
    have hD_nat : (coverageSymmDiff x z ((differingThresholds x z).min' hne_xz)).Nonempty := by
      unfold differingThresholds; rw [← lift_xz.1]; exact hSD_ne
    refine ⟨hne_xz, hD_nat, ?_⟩
    unfold differingThresholds
    rw [← lift_xz.2, ← Finset.min'_of_eq lift_xz.1 hSD_ne hD_nat]
    exact hverd
  -- Three cases on a₁ vs a₂
  rcases lt_trichotomy a₁ a₂ with h_lt | h_eq | h_gt
  · -- Case a₁ < a₂: coverage of y and z agree at a₁
    have hyz_eq : coverageSet y a₁ = coverageSet z a₁ := agree_yz a₁ ha₁_T h_lt
    have hxz_ne : coverageSet x a₁ ≠ coverageSet z a₁ := by
      rw [← hyz_eq]; exact (Finset.mem_filter.mp (Finset.min'_mem Dxy hDxy_ne)).2
    have ha₁_Dxz : a₁ ∈ Dxz := Finset.mem_filter.mpr ⟨ha₁_T, hxz_ne⟩
    have ha₁_min : ∀ t, t ∈ Dxz → a₁ ≤ t := by
      intro t ht
      have := dxz_lower_bound t ht
      rwa [min_eq_left (le_of_lt h_lt)] at this
    obtain ⟨hDxz_ne, hmin_eq⟩ := min_dxz a₁ ha₁_Dxz ha₁_min
    have hSD_chain : coverageSymmDiff x z (Dxz.min' hDxz_ne) = coverageSymmDiff x y a₁ := by
      rw [congr_arg (coverageSymmDiff x z) hmin_eq]
      simp only [coverageSymmDiff, hyz_eq]
    have hCS_chain : coverageSet x (Dxz.min' hDxz_ne) = coverageSet x a₁ :=
      congr_arg (coverageSet x) hmin_eq
    have hSD_ne : (coverageSymmDiff x z (Dxz.min' hDxz_ne)).Nonempty := hSD_chain ▸ hSD1_ne
    refine ⟨hDxz_ne, hSD_ne, ?_⟩
    rw [Finset.min'_of_eq hSD_chain hSD_ne hSD1_ne, hCS_chain]
    exact hv1
  · -- Case a₁ = a₂: use symmDiff_min_trans at threshold a₁
    have heq_yz : coverageSymmDiff y z a₁ = coverageSymmDiff y z a₂ :=
      congr_arg (coverageSymmDiff y z) h_eq
    have hSD2_ne' : (coverageSymmDiff y z a₁).Nonempty := heq_yz ▸ hSD2_ne
    have hv2' : (coverageSymmDiff y z a₁).min' hSD2_ne' ∈ coverageSet y a₁ := by
      rw [Finset.min'_of_eq heq_yz hSD2_ne' hSD2_ne, congr_arg (coverageSet y) h_eq]
      exact hv2
    obtain ⟨hSD_xz_ne, hverd_xz⟩ := symmDiff_min_trans hSD1_ne hSD2_ne' hv1 hv2'
    -- H(x) △ H(z) nonempty at a₁, so coverage sets differ
    have hxz_ne : coverageSet x a₁ ≠ coverageSet z a₁ := by
      intro heq; rw [heq, symmDiff_self] at hSD_xz_ne
      exact absurd hSD_xz_ne (by simp)
    have ha₁_Dxz : a₁ ∈ Dxz := Finset.mem_filter.mpr ⟨ha₁_T, hxz_ne⟩
    have ha₁_min : ∀ t, t ∈ Dxz → a₁ ≤ t := by
      intro t ht
      have := dxz_lower_bound t ht
      rwa [min_eq_left (le_of_eq h_eq)] at this
    obtain ⟨hDxz_ne, hmin_eq⟩ := min_dxz a₁ ha₁_Dxz ha₁_min
    have hSD_chain : coverageSymmDiff x z (Dxz.min' hDxz_ne) = coverageSymmDiff x z a₁ :=
      congr_arg (coverageSymmDiff x z) hmin_eq
    have hCS_chain : coverageSet x (Dxz.min' hDxz_ne) = coverageSet x a₁ :=
      congr_arg (coverageSet x) hmin_eq
    have hSD_ne : (coverageSymmDiff x z (Dxz.min' hDxz_ne)).Nonempty := hSD_chain ▸ hSD_xz_ne
    refine ⟨hDxz_ne, hSD_ne, ?_⟩
    rw [Finset.min'_of_eq hSD_chain hSD_ne hSD_xz_ne, hCS_chain]
    exact hverd_xz
  · -- Case a₂ < a₁: coverage of x and y agree at a₂
    have hxy_eq : coverageSet x a₂ = coverageSet y a₂ := agree_xy a₂ ha₂_T h_gt
    have hxz_ne : coverageSet x a₂ ≠ coverageSet z a₂ := by
      rw [hxy_eq]; exact (Finset.mem_filter.mp (Finset.min'_mem Dyz hDyz_ne)).2
    have ha₂_Dxz : a₂ ∈ Dxz := Finset.mem_filter.mpr ⟨ha₂_T, hxz_ne⟩
    have ha₂_min : ∀ t, t ∈ Dxz → a₂ ≤ t := by
      intro t ht
      have := dxz_lower_bound t ht
      rwa [min_eq_right (le_of_lt h_gt)] at this
    obtain ⟨hDxz_ne, hmin_eq⟩ := min_dxz a₂ ha₂_Dxz ha₂_min
    have hSD_chain : coverageSymmDiff x z (Dxz.min' hDxz_ne) = coverageSymmDiff y z a₂ := by
      rw [congr_arg (coverageSymmDiff x z) hmin_eq]
      simp only [coverageSymmDiff, hxy_eq]
    have hCS_chain : coverageSet x (Dxz.min' hDxz_ne) = coverageSet x a₂ :=
      congr_arg (coverageSet x) hmin_eq
    have hSD_ne : (coverageSymmDiff x z (Dxz.min' hDxz_ne)).Nonempty := hSD_chain ▸ hSD2_ne
    refine ⟨hDxz_ne, hSD_ne, ?_⟩
    rw [Finset.min'_of_eq hSD_chain hSD_ne hSD2_ne, hCS_chain, hxy_eq]
    exact hv2

theorem PPROT_satisfies_T {n : ℕ} : Ax_T (@PPROT n) := by
  intro x y z hxy hyz
  rcases hxy with rfl | hxy_s
  · exact hyz
  · rcases hyz with rfl | hyz_s
    · exact Or.inr hxy_s
    · by_cases hxz : x = z
      · subst hxz
        exfalso
        obtain ⟨hne1, hD1, hr1⟩ := hxy_s
        obtain ⟨hne2, hD2, hr2⟩ := hyz_s
        have ha_eq : (differingThresholds y x).min' hne2 =
            (differingThresholds x y).min' hne1 :=
          Finset.min'_of_eq (differingThresholds_comm y x) hne2 hne1
        have hD_eq : coverageSymmDiff y x ((differingThresholds y x).min' hne2) =
            coverageSymmDiff x y ((differingThresholds x y).min' hne1) := by
          rw [ha_eq]; exact coverageSymmDiff_comm y x _
        have hD2' : (coverageSymmDiff x y ((differingThresholds x y).min' hne1)).Nonempty :=
          hD_eq ▸ hD2
        have hr_eq := Finset.min'_of_eq hD_eq hD2 hD1
        rw [hr_eq, ha_eq] at hr2
        have hr_mem := Finset.min'_mem _ hD1
        unfold coverageSymmDiff at hr_mem
        rw [Finset.mem_symmDiff] at hr_mem
        rcases hr_mem with ⟨_, hny⟩ | ⟨_, hnx⟩
        · exact hny hr2
        · exact hnx hr1
      · exact Or.inr (pprot_strict_trans x y z hxz hxy_s hyz_s)

theorem PPROT_satisfies_PD {n : ℕ} : Ax_PD (@PPROT n) := by
  intro x y hge hstrict
  have hne : x ≠ y := by
    intro h; obtain ⟨j, hj⟩ := hstrict; rw [h] at hj; linarith
  constructor
  · -- PPROT x y: at any threshold, H_a(y) ⊆ H_a(x), so symm diff ⊆ H_a(x)
    right
    have hne_dt := differingThresholds_nonempty x y hne
    have ha_ne := (Finset.mem_filter.mp (Finset.min'_mem _ hne_dt)).2
    have hD := symmDiff_nonempty_of_ne x y _ ha_ne
    refine ⟨hne_dt, hD, ?_⟩
    have hr := Finset.min'_mem _ hD
    unfold coverageSymmDiff at hr
    rw [Finset.mem_symmDiff] at hr
    rcases hr with ⟨hx, _⟩ | ⟨hy, hx⟩
    · exact hx
    · exfalso; apply hx; rw [mem_coverageSet] at hy ⊢; exact le_trans hy (hge _)
  · -- ¬ PPROT y x
    intro hyx
    rcases hyx with rfl | ⟨hne_yx, hD_yx, hr_yx⟩
    · obtain ⟨j, hj⟩ := hstrict; linarith [hge j]
    · have hr := Finset.min'_mem _ hD_yx
      unfold coverageSymmDiff at hr
      rw [Finset.mem_symmDiff] at hr
      rcases hr with ⟨hy_in, hx_out⟩ | ⟨hx_in, hy_out⟩
      · exact hx_out (by rw [mem_coverageSet] at hy_in ⊢; exact le_trans hy_in (hge _))
      · exact hy_out hr_yx

theorem PPROT_satisfies_NUTC {n : ℕ} : Ax_NUTC (@PPROT n) := by
  intro x y _hxy hne hD hr_in_x
  -- min(D at a*_min) ∈ H_{a*}(x) means PPROT_strict x y
  have hpprot_xy : PPROT_strict x y := ⟨hne, hD, hr_in_x⟩
  -- ¬ strictPart PPROT y x
  intro ⟨_, hnotRxy⟩
  exact hnotRxy (Or.inr hpprot_xy)

/-! ## Reverse: C + T + PD + NUTC ⟹ R = PPROT -/

/-- Step 1: NUTC + C give weak preference when min(D) ∈ H_{a*}(x). -/
private theorem nutc_weak {n : ℕ} {R : PrefRel n}
    (hC : Ax_C R) (hNUTC : Ax_NUTC R)
    (x y : Vec n) (hne_xy : x ≠ y)
    (hne : (differingThresholds x y).Nonempty)
    (hD : (coverageSymmDiff x y ((differingThresholds x y).min' hne)).Nonempty)
    (hr : (coverageSymmDiff x y ((differingThresholds x y).min' hne)).min' hD ∈
      coverageSet x ((differingThresholds x y).min' hne)) :
    R x y := by
  have h_not_yx := hNUTC x y hne_xy hne hD hr
  rcases hC x y with h | h
  · exact h
  · by_contra hnotRxy; exact h_not_yx ⟨h, hnotRxy⟩

/-- Technical lemma: r* is in H_{a*}(x) but not in H_{a*}(y). -/
private theorem rstar_in_x_not_y {n : ℕ} (x y : Vec n)
    (hne : (differingThresholds x y).Nonempty)
    (hD : (coverageSymmDiff x y ((differingThresholds x y).min' hne)).Nonempty)
    (hr : (coverageSymmDiff x y ((differingThresholds x y).min' hne)).min' hD ∈
      coverageSet x ((differingThresholds x y).min' hne)) :
    (coverageSymmDiff x y ((differingThresholds x y).min' hne)).min' hD ∉
      coverageSet y ((differingThresholds x y).min' hne) := by
  set a_star := (differingThresholds x y).min' hne
  set r_star := (coverageSymmDiff x y a_star).min' hD
  have hr_mem := Finset.min'_mem _ hD
  unfold coverageSymmDiff at hr_mem
  rw [Finset.mem_symmDiff] at hr_mem
  rcases hr_mem with ⟨_, hny⟩ | ⟨hy, hnx⟩
  · exact hny
  · exfalso; exact hnx hr

/-- Helper: in any open real interval (a,b), there exists a point not in a given finite set. -/
private theorem exists_between_avoiding_finset (a b : ℝ) (hab : a < b) (S : Finset ℝ) :
    ∃ c, a < c ∧ c < b ∧ c ∉ S := by
  -- The interval (a,b) is infinite, S is finite, so some point avoids S.
  -- We prove by finding a point: take the midpoint, or shift to avoid S.
  by_cases hS : (S.filter (fun s => a < s ∧ s < b)).Nonempty
  · -- There are elements of S in (a,b). Pick a point below the minimum.
    set T := S.filter (fun s => a < s ∧ s < b)
    have hTne := hS
    set m := T.min' hTne
    have hm_mem := Finset.min'_mem T hTne
    rw [Finset.mem_filter] at hm_mem
    have hm_gt : a < m := hm_mem.2.1
    -- Use the midpoint of (a, m)
    refine ⟨(a + m) / 2, by linarith, by linarith, ?_⟩
    intro hmid_in
    have hmid_in_T : (a + m) / 2 ∈ T := by
      rw [Finset.mem_filter]; exact ⟨hmid_in, by constructor <;> linarith⟩
    have := Finset.min'_le T _ hmid_in_T
    linarith
  · -- No elements of S in (a,b). The midpoint works.
    rw [Finset.not_nonempty_iff_eq_empty] at hS
    refine ⟨(a + b) / 2, by linarith, by linarith, ?_⟩
    intro hmid_in
    have : (a + b) / 2 ∈ S.filter (fun s => a < s ∧ s < b) :=
      Finset.mem_filter.mpr ⟨hmid_in, by constructor <;> linarith⟩
    rw [hS] at this; simp at this

/-- No threshold value of (x,y) lies in the open interval (y_{r*}, a*).
    Any such value would be a differing threshold below a*, contradicting minimality. -/
private theorem no_threshold_in_gap {n : ℕ} (x y : Vec n)
    (hne : (differingThresholds x y).Nonempty)
    (hD : (coverageSymmDiff x y ((differingThresholds x y).min' hne)).Nonempty)
    (hr : (coverageSymmDiff x y ((differingThresholds x y).min' hne)).min' hD ∈
      coverageSet x ((differingThresholds x y).min' hne)) :
    let a_star := (differingThresholds x y).min' hne
    let r_star := (coverageSymmDiff x y a_star).min' hD
    ∀ t ∈ thresholdValues x y, ¬(y r_star < t ∧ t < a_star) := by
  intro a_star r_star t ht ⟨hgt, hlt⟩
  have hxr_ge : x r_star ≥ a_star := (mem_coverageSet x a_star r_star).mp hr
  have hr_not_y := rstar_in_x_not_y x y hne hD hr
  have hr_in_x : r_star ∈ coverageSet x t := by
    rw [mem_coverageSet]; linarith
  have hr_not_y_t : r_star ∉ coverageSet y t := by
    rw [mem_coverageSet]; push_neg
    rw [mem_coverageSet] at hr_not_y; push_neg at hr_not_y; linarith
  have hne_cov : coverageSet x t ≠ coverageSet y t := by
    intro heq; rw [heq] at hr_in_x; exact hr_not_y_t hr_in_x
  have ht_diff : t ∈ differingThresholds x y := by
    simp only [differingThresholds, Finset.mem_filter]; exact ⟨ht, hne_cov⟩
  linarith [Finset.min'_le _ t ht_diff]

/-- Step 2: The perturbation argument upgrades weak to strict preference.
    Key idea: decrease x_{r*} to a value c in the gap (y_{r*}, a*). Since no
    threshold value lies in this gap, coverage at c equals coverage at a*,
    making NUTC applicable to the perturbed pair. -/
private theorem nutc_strict {n : ℕ} {R : PrefRel n}
    (hC : Ax_C R) (hT : Ax_T R) (hPD : Ax_PD R) (hNUTC : Ax_NUTC R)
    (x y : Vec n) (hne_xy : x ≠ y)
    (hne : (differingThresholds x y).Nonempty)
    (hD : (coverageSymmDiff x y ((differingThresholds x y).min' hne)).Nonempty)
    (hr : (coverageSymmDiff x y ((differingThresholds x y).min' hne)).min' hD ∈
      coverageSet x ((differingThresholds x y).min' hne)) :
    strictPart R x y := by
  have hRxy := nutc_weak hC hNUTC x y hne_xy hne hD hr
  constructor
  · exact hRxy
  · intro hRyx
    -- Setup: names for a*, r*
    set a_star := (differingThresholds x y).min' hne
    set r_star := (coverageSymmDiff x y a_star).min' hD
    -- r* ∈ H_{a*}(x) \ H_{a*}(y)
    have hxr_ge : x r_star ≥ a_star := (mem_coverageSet x a_star r_star).mp hr
    have hr_not_y := rstar_in_x_not_y x y hne hD hr
    have hyr_lt : y r_star < a_star := by
      rw [mem_coverageSet] at hr_not_y; push_neg at hr_not_y; exact hr_not_y
    -- No threshold value in (y_{r*}, a*)
    have no_gap := no_threshold_in_gap x y hne hD hr
    -- Threshold dichotomy: every threshold value is ≤ y_{r*} or ≥ a*
    have threshold_dichotomy : ∀ t ∈ thresholdValues x y, t ≤ y r_star ∨ t ≥ a_star := by
      intro t ht; by_contra h; push_neg at h; exact no_gap t ht h
    have x_dichotomy : ∀ i : Fin n, x i ≤ y r_star ∨ x i ≥ a_star := by
      intro i; apply threshold_dichotomy
      simp only [thresholdValues, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl ⟨i, rfl⟩
    have y_dichotomy : ∀ i : Fin n, y i ≤ y r_star ∨ y i ≥ a_star := by
      intro i; apply threshold_dichotomy
      simp only [thresholdValues, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inr ⟨i, rfl⟩
    -- Choose c in the gap (y_{r*}, a*) — midpoint works since gap has no T values
    set c := (y r_star + a_star) / 2 with hc_def
    have hc_gt : y r_star < c := by linarith
    have hc_lt : c < a_star := by linarith
    -- Construct x_eps: decrease x_{r*} to c, keep other coordinates
    set x_eps : Vec n := fun i => if i = r_star then c else x i with hx_eps_def
    -- x Pareto-dominates x_eps (x_{r*} ≥ a* > c, other coords equal)
    have hge_x_xe : ∀ i : Fin n, x i ≥ x_eps i := by
      intro i; simp only [hx_eps_def]; split_ifs with h
      · subst h; linarith
      · linarith
    have hstrict_x_xe : x r_star > x_eps r_star := by
      simp only [hx_eps_def, if_pos rfl]; linarith
    -- PD: x ≻ x_eps
    have hPD_x_xe : strictPart R x x_eps := hPD x x_eps hge_x_xe ⟨r_star, hstrict_x_xe⟩
    -- T + indifference: y ≻ x_eps
    have hR_y_xe : R y x_eps := hT y x x_eps hRyx hPD_x_xe.1
    have hR_xe_y_false : ¬ R x_eps y :=
      fun h => hPD_x_xe.2 (hT x_eps y x h hRyx)
    have hstrict_y_xe : strictPart R y x_eps := ⟨hR_y_xe, hR_xe_y_false⟩
    -- x_eps ≠ y
    have hne_xe_y : x_eps ≠ y := by
      intro h; have := congr_fun h r_star
      simp only [hx_eps_def, if_pos rfl] at this; linarith
    -- Coverage at c: H_c(x_eps) = H_{a*}(x) and H_c(y) = H_{a*}(y)
    -- Because no T value in (y_{r*}, a*): for v ∈ {x,y}, v_i ≥ c ↔ v_i ≥ a*
    have hcov_c_xe : coverageSet x_eps c = coverageSet x a_star := by
      ext i; simp only [coverageSet, Finset.mem_filter, Finset.mem_univ, true_and, hx_eps_def]
      split_ifs with h
      · subst h; exact ⟨fun _ => hxr_ge, fun _ => le_refl c⟩
      · constructor
        · intro hge; rcases x_dichotomy i with hle | hge'
          · linarith
          · exact hge'
        · intro hge; linarith
    have hcov_c_y : coverageSet y c = coverageSet y a_star := by
      ext i; simp only [coverageSet, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hge; rcases y_dichotomy i with hle | hge'
        · linarith
        · exact hge'
      · intro hge; linarith
    -- c is a differing threshold for (x_eps, y) with same symm diff as a* for (x, y)
    have hcov_ne : coverageSet x_eps c ≠ coverageSet y c := by
      rw [hcov_c_xe, hcov_c_y]
      exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
    have hc_in_tv : c ∈ thresholdValues x_eps y := by
      simp only [thresholdValues, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl ⟨r_star, by simp [hx_eps_def]⟩
    have hc_diff : c ∈ differingThresholds x_eps y :=
      Finset.mem_filter.mpr ⟨hc_in_tv, hcov_ne⟩
    -- c is the MINIMUM differing threshold for (x_eps, y)
    have hc_min : ∀ b ∈ differingThresholds x_eps y, c ≤ b := by
      intro b hb
      by_contra hlt; push_neg at hlt
      obtain ⟨hb_tv, hb_ne⟩ := Finset.mem_filter.mp hb
      -- b < c, b ∈ thresholdValues(x_eps, y). Show b ∈ thresholdValues(x, y).
      have hb_in_T : b ∈ thresholdValues x y := by
        simp only [thresholdValues, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
          true_and] at hb_tv ⊢
        rcases hb_tv with ⟨i, hi⟩ | ⟨i, hi⟩
        · simp only [hx_eps_def] at hi
          split_ifs at hi with h
          · subst h; linarith  -- b = c, contradicts b < c
          · exact Or.inl ⟨i, hi⟩
        · exact Or.inr ⟨i, hi⟩
      -- H_b(x_eps) = H_b(x) (since (x_eps)_{r*} = c > b and x_{r*} ≥ a* > b)
      have hcov_xe_x : coverageSet x_eps b = coverageSet x b := by
        ext i; simp only [coverageSet, Finset.mem_filter, Finset.mem_univ, true_and, hx_eps_def]
        split_ifs with h
        · subst h; exact ⟨fun _ => by linarith, fun _ => by linarith⟩
        · exact Iff.rfl
      -- H_b(x) = H_b(y) (since b ∈ T and b < c < a*)
      have hcov_x_y : coverageSet x b = coverageSet y b := by
        by_contra hne_b
        have hb_diff : b ∈ differingThresholds x y :=
          Finset.mem_filter.mpr ⟨hb_in_T, hne_b⟩
        linarith [Finset.min'_le _ b hb_diff]
      exact hb_ne (hcov_xe_x.trans hcov_x_y)
    -- Assemble NUTC application on (x_eps, y)
    have hne_dt_xe : (differingThresholds x_eps y).Nonempty := ⟨c, hc_diff⟩
    have hmin_eq : (differingThresholds x_eps y).min' hne_dt_xe = c :=
      le_antisymm (Finset.min'_le _ c hc_diff) (hc_min _ (Finset.min'_mem _ hne_dt_xe))
    -- Symm diff at c for (x_eps, y) = symm diff at a* for (x, y)
    have hD_eq : coverageSymmDiff x_eps y c = coverageSymmDiff x y a_star := by
      simp only [coverageSymmDiff]; rw [hcov_c_xe, hcov_c_y]
    have hD_xe : (coverageSymmDiff x_eps y
        ((differingThresholds x_eps y).min' hne_dt_xe)).Nonempty := by
      rw [hmin_eq]; exact hD_eq ▸ hD
    have hr_xe : (coverageSymmDiff x_eps y
        ((differingThresholds x_eps y).min' hne_dt_xe)).min' hD_xe ∈
        coverageSet x_eps ((differingThresholds x_eps y).min' hne_dt_xe) := by
      have h1 : coverageSymmDiff x_eps y
          ((differingThresholds x_eps y).min' hne_dt_xe) =
          coverageSymmDiff x y a_star := by rw [hmin_eq]; exact hD_eq
      have h2 : (coverageSymmDiff x_eps y
          ((differingThresholds x_eps y).min' hne_dt_xe)).min' hD_xe = r_star :=
        Finset.min'_of_eq h1 hD_xe hD
      rw [h2, hmin_eq, hcov_c_xe]; exact hr
    exact hNUTC x_eps y hne_xe_y hne_dt_xe hD_xe hr_xe hstrict_y_xe

theorem C_T_PD_NUTC_imp_PPROT {n : ℕ} {R : PrefRel n}
    (hC : Ax_C R) (hT : Ax_T R) (hPD : Ax_PD R) (hNUTC : Ax_NUTC R) :
    ∀ x y, R x y ↔ PPROT x y := by
  intro x y
  constructor
  · -- R x y → PPROT x y
    intro hRxy
    by_cases heq : x = y
    · exact Or.inl heq
    · have hne := differingThresholds_nonempty x y heq
      have ha_ne := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
      have hD := symmDiff_nonempty_of_ne x y _ ha_ne
      have hr_mem := Finset.min'_mem _ hD
      unfold coverageSymmDiff at hr_mem
      rw [Finset.mem_symmDiff] at hr_mem
      rcases hr_mem with ⟨hx, _⟩ | ⟨hy, _⟩
      · exact Or.inr ⟨hne, hD, hx⟩
      · -- min(D) ∈ H_{a*}(y): NUTC on (y,x) gives ¬(x ≻ y), so R y x.
        -- Then nutc_strict on (y,x) gives y ≻ x, contradicting R x y.
        exfalso
        have hne_yx : y ≠ x := fun h => heq h.symm
        have hne_dt_yx : (differingThresholds y x).Nonempty := by
          rw [differingThresholds_comm]; exact hne
        have ha_eq : (differingThresholds y x).min' hne_dt_yx =
            (differingThresholds x y).min' hne :=
          Finset.min'_of_eq (differingThresholds_comm y x) hne_dt_yx hne
        have hD_eq : coverageSymmDiff y x ((differingThresholds y x).min' hne_dt_yx) =
            coverageSymmDiff x y ((differingThresholds x y).min' hne) := by
          rw [ha_eq]; exact coverageSymmDiff_comm y x _
        have hD_yx : (coverageSymmDiff y x ((differingThresholds y x).min' hne_dt_yx)).Nonempty :=
          hD_eq ▸ hD
        have hr_eq := Finset.min'_of_eq hD_eq hD_yx hD
        have hy_in : (coverageSymmDiff y x ((differingThresholds y x).min' hne_dt_yx)).min' hD_yx ∈
            coverageSet y ((differingThresholds y x).min' hne_dt_yx) := by
          rw [hr_eq, ha_eq]; exact hy
        exact (nutc_strict hC hT hPD hNUTC y x hne_yx hne_dt_yx hD_yx hy_in).2 hRxy
  · -- PPROT x y → R x y
    intro hPPROT
    rcases hPPROT with rfl | ⟨hne_dt, hD, hr⟩
    · rcases hC x x with h | h <;> exact h
    · have hne_xy : x ≠ y := by
        intro h; subst h
        have := Finset.min'_mem _ hne_dt
        simp [differingThresholds] at this
      exact (nutc_strict hC hT hPD hNUTC x y hne_xy hne_dt hD hr).1

/-! ## Main characterization -/

/-- **Theorem 5'**: A preference is P-PROT iff it satisfies C, T, PD, and NUTC. -/
theorem PPROT_NUTC_characterization {n : ℕ} {R : PrefRel n} :
    (∀ x y, R x y ↔ PPROT x y) ↔ (Ax_C R ∧ Ax_T R ∧ Ax_PD R ∧ Ax_NUTC R) := by
  constructor
  · intro hR
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Completeness
      intro x y
      rcases PPROT_satisfies_C x y with h | h
      · exact Or.inl ((hR x y).mpr h)
      · exact Or.inr ((hR y x).mpr h)
    · -- Transitivity
      intro x y z hxy hyz
      exact (hR x z).mpr (PPROT_satisfies_T x y z ((hR x y).mp hxy) ((hR y z).mp hyz))
    · -- Pareto Dominance
      intro x y hge hstrict
      have h := PPROT_satisfies_PD x y hge hstrict
      exact ⟨(hR x y).mpr h.1, fun hR' => h.2 ((hR y x).mp hR')⟩
    · -- NUTC
      intro x y hxy hne hD hr
      intro hstrict
      have hstrict_pprot : strictPart PPROT y x :=
        ⟨(hR y x).mp hstrict.1, fun h => hstrict.2 ((hR x y).mpr h)⟩
      exact PPROT_satisfies_NUTC x y hxy hne hD hr hstrict_pprot
  · rintro ⟨hC, hT, hPD, hNUTC⟩
    exact C_T_PD_NUTC_imp_PPROT hC hT hPD hNUTC
