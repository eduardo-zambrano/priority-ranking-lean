/-
  PriorityRanking.Characterizations.QPROT_NDTC
  Theorem: Q-PROT = C + T + PD + NDTC.

  Q-PROT is characterized by exactly four axioms:
  Completeness, Transitivity, Pareto Dominance, and
  No Downward Threshold Compensation.

  Strategy: leverage the existing C + HTSF characterization.
  1. Show C + HTSF ⟹ C + T + PD + NDTC (Q-PROT is a weak order, etc.)
  2. Show C + T + PD + NDTC ⟹ R = Q-PROT (the hard direction)

  Mirrors PPROT_NUTC.lean with min → max throughout.
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms
import LeanFormalization.Characterizations.QPROT

open Finset

/-! ## Forward: Q-PROT satisfies T, PD, NDTC -/

/-- Transitivity of Q-PROT strict preference via universal threshold sets.
    Mirrors pprot_strict_trans but uses max' for differing thresholds. -/
private theorem qprot_strict_trans {n : ℕ} (x y z : Vec n) (hxz : x ≠ z)
    (hxy : QPROT_strict x y) (hyz : QPROT_strict y z) : QPROT_strict x z := by
  obtain ⟨hne_xy, hD_xy, hr_xy⟩ := hxy
  obtain ⟨hne_yz, hD_yz, hr_yz⟩ := hyz
  set T := thresholdValues x y ∪ thresholdValues y z
  set Dxy := T.filter (fun a => coverageSet x a ≠ coverageSet y a)
  set Dyz := T.filter (fun a => coverageSet y a ≠ coverageSet z a)
  set Dxz := T.filter (fun a => coverageSet x a ≠ coverageSet z a)
  have hxy_sub : thresholdValues x y ⊆ T := Finset.subset_union_left
  have hyz_sub : thresholdValues y z ⊆ T := Finset.subset_union_right
  have hxz_sub : thresholdValues x z ⊆ T := by
    intro t ht
    rcases Finset.mem_union.mp ht with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr h)))
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
  have hDxy_ne : Dxy.Nonempty := by
    obtain ⟨a, ha⟩ := hne_xy
    exact ⟨a, Finset.mem_filter.mpr
      ⟨hxy_sub (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩⟩
  have hDyz_ne : Dyz.Nonempty := by
    obtain ⟨a, ha⟩ := hne_yz
    exact ⟨a, Finset.mem_filter.mpr
      ⟨hyz_sub (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩⟩
  -- Lift verdicts using enlarged_symmDiff_eq_max
  have lift_xy := enlarged_symmDiff_eq_max x y _ T hxy_sub hx_xy hy_xy hne_xy hDxy_ne
  have lift_yz := enlarged_symmDiff_eq_max y z _ T hyz_sub hy_yz hz_yz hne_yz hDyz_ne
  set a₁ := Dxy.max' hDxy_ne
  set a₂ := Dyz.max' hDyz_ne
  have hSD1_ne : (coverageSymmDiff x y a₁).Nonempty := lift_xy.1 ▸ hD_xy
  have hSD2_ne : (coverageSymmDiff y z a₂).Nonempty := lift_yz.1 ▸ hD_yz
  have hv1 : (coverageSymmDiff x y a₁).min' hSD1_ne ∈ coverageSet x a₁ := by
    rw [Finset.min'_of_eq lift_xy.1 hSD1_ne hD_xy, lift_xy.2]; exact hr_xy
  have hv2 : (coverageSymmDiff y z a₂).min' hSD2_ne ∈ coverageSet y a₂ := by
    rw [Finset.min'_of_eq lift_yz.1 hSD2_ne hD_yz, lift_yz.2]; exact hr_yz
  -- Agreement above max differing threshold
  have agree_xy : ∀ t, t ∈ T → a₁ < t → coverageSet x t = coverageSet y t := by
    intro t ht hlt; by_contra h
    exact absurd (Finset.le_max' _ t (Finset.mem_filter.mpr ⟨ht, h⟩)) (not_le.mpr hlt)
  have agree_yz : ∀ t, t ∈ T → a₂ < t → coverageSet y t = coverageSet z t := by
    intro t ht hlt; by_contra h
    exact absurd (Finset.le_max' _ t (Finset.mem_filter.mpr ⟨ht, h⟩)) (not_le.mpr hlt)
  have ha₁_T : a₁ ∈ T := (Finset.mem_filter.mp (Finset.max'_mem Dxy hDxy_ne)).1
  have ha₂_T : a₂ ∈ T := (Finset.mem_filter.mp (Finset.max'_mem Dyz hDyz_ne)).1
  have no_above : ∀ t, t ∈ T → a₁ < t → a₂ < t → coverageSet x t = coverageSet z t :=
    fun t ht h1 h2 => (agree_xy t ht h1).trans (agree_yz t ht h2)
  -- Helper: Dxz.max' = a for given a ∈ Dxz when no Dxz element above a
  have max_dxz (a : ℝ) (ha : a ∈ Dxz) (habove : ∀ t, t ∈ Dxz → t ≤ a) :
      ∃ (hne : Dxz.Nonempty), Dxz.max' hne = a :=
    ⟨⟨a, ha⟩, le_antisymm (habove _ (Finset.max'_mem _ ⟨a, ha⟩)) (Finset.le_max' _ _ ha)⟩
  -- No Dxz element above max(a₁, a₂)
  have dxz_upper_bound : ∀ t, t ∈ Dxz → t ≤ max a₁ a₂ := by
    intro t ht
    by_contra hlt; push_neg at hlt
    have ht_T := (Finset.mem_filter.mp ht).1
    exact (Finset.mem_filter.mp ht).2
      (no_above t ht_T (lt_of_le_of_lt (le_max_left _ _) hlt)
        (lt_of_le_of_lt (le_max_right _ _) hlt))
  suffices h : ∃ (hne : Dxz.Nonempty),
      ∃ (hD : (coverageSymmDiff x z (Dxz.max' hne)).Nonempty),
        (coverageSymmDiff x z (Dxz.max' hne)).min' hD ∈ coverageSet x (Dxz.max' hne) by
    obtain ⟨hDxz_ne, hSD_ne, hverd⟩ := h
    have hne_xz := differingThresholds_nonempty x z hxz
    have lift_xz := enlarged_symmDiff_eq_max x z _ T hxz_sub hx_xz hz_xz hne_xz hDxz_ne
    have hD_nat : (coverageSymmDiff x z ((differingThresholds x z).max' hne_xz)).Nonempty := by
      unfold differingThresholds; rw [← lift_xz.1]; exact hSD_ne
    refine ⟨hne_xz, hD_nat, ?_⟩
    unfold differingThresholds
    rw [← lift_xz.2, ← Finset.min'_of_eq lift_xz.1 hSD_ne hD_nat]
    exact hverd
  rcases lt_trichotomy a₁ a₂ with h_lt | h_eq | h_gt
  · -- Case a₁ < a₂: coverage of x and y agree at a₂
    have hxy_eq : coverageSet x a₂ = coverageSet y a₂ := agree_xy a₂ ha₂_T h_lt
    have hxz_ne : coverageSet x a₂ ≠ coverageSet z a₂ := by
      rw [hxy_eq]; exact (Finset.mem_filter.mp (Finset.max'_mem Dyz hDyz_ne)).2
    have ha₂_Dxz : a₂ ∈ Dxz := Finset.mem_filter.mpr ⟨ha₂_T, hxz_ne⟩
    have ha₂_max : ∀ t, t ∈ Dxz → t ≤ a₂ := by
      intro t ht
      have := dxz_upper_bound t ht
      rwa [max_eq_right (le_of_lt h_lt)] at this
    obtain ⟨hDxz_ne, hmax_eq⟩ := max_dxz a₂ ha₂_Dxz ha₂_max
    have hSD_chain : coverageSymmDiff x z (Dxz.max' hDxz_ne) = coverageSymmDiff y z a₂ := by
      rw [congr_arg (coverageSymmDiff x z) hmax_eq]
      simp only [coverageSymmDiff, hxy_eq]
    have hCS_chain : coverageSet x (Dxz.max' hDxz_ne) = coverageSet x a₂ :=
      congr_arg (coverageSet x) hmax_eq
    have hSD_ne : (coverageSymmDiff x z (Dxz.max' hDxz_ne)).Nonempty := hSD_chain ▸ hSD2_ne
    refine ⟨hDxz_ne, hSD_ne, ?_⟩
    rw [Finset.min'_of_eq hSD_chain hSD_ne hSD2_ne, hCS_chain, hxy_eq]
    exact hv2
  · -- Case a₁ = a₂: use symmDiff_min_trans at threshold a₁
    have heq_yz : coverageSymmDiff y z a₁ = coverageSymmDiff y z a₂ :=
      congr_arg (coverageSymmDiff y z) h_eq
    have hSD2_ne' : (coverageSymmDiff y z a₁).Nonempty := heq_yz ▸ hSD2_ne
    have hv2' : (coverageSymmDiff y z a₁).min' hSD2_ne' ∈ coverageSet y a₁ := by
      rw [Finset.min'_of_eq heq_yz hSD2_ne' hSD2_ne, congr_arg (coverageSet y) h_eq]
      exact hv2
    obtain ⟨hSD_xz_ne, hverd_xz⟩ := symmDiff_min_trans hSD1_ne hSD2_ne' hv1 hv2'
    have hxz_ne : coverageSet x a₁ ≠ coverageSet z a₁ := by
      intro heq; rw [heq, symmDiff_self] at hSD_xz_ne
      exact absurd hSD_xz_ne (by simp)
    have ha₁_Dxz : a₁ ∈ Dxz := Finset.mem_filter.mpr ⟨ha₁_T, hxz_ne⟩
    have ha₁_max : ∀ t, t ∈ Dxz → t ≤ a₁ := by
      intro t ht
      have := dxz_upper_bound t ht
      rwa [max_eq_left (le_of_eq h_eq.symm)] at this
    obtain ⟨hDxz_ne, hmax_eq⟩ := max_dxz a₁ ha₁_Dxz ha₁_max
    have hSD_chain : coverageSymmDiff x z (Dxz.max' hDxz_ne) = coverageSymmDiff x z a₁ :=
      congr_arg (coverageSymmDiff x z) hmax_eq
    have hCS_chain : coverageSet x (Dxz.max' hDxz_ne) = coverageSet x a₁ :=
      congr_arg (coverageSet x) hmax_eq
    have hSD_ne : (coverageSymmDiff x z (Dxz.max' hDxz_ne)).Nonempty := hSD_chain ▸ hSD_xz_ne
    refine ⟨hDxz_ne, hSD_ne, ?_⟩
    rw [Finset.min'_of_eq hSD_chain hSD_ne hSD_xz_ne, hCS_chain]
    exact hverd_xz
  · -- Case a₂ < a₁: coverage of y and z agree at a₁
    have hyz_eq : coverageSet y a₁ = coverageSet z a₁ := agree_yz a₁ ha₁_T h_gt
    have hxz_ne : coverageSet x a₁ ≠ coverageSet z a₁ := by
      rw [← hyz_eq]; exact (Finset.mem_filter.mp (Finset.max'_mem Dxy hDxy_ne)).2
    have ha₁_Dxz : a₁ ∈ Dxz := Finset.mem_filter.mpr ⟨ha₁_T, hxz_ne⟩
    have ha₁_max : ∀ t, t ∈ Dxz → t ≤ a₁ := by
      intro t ht
      have := dxz_upper_bound t ht
      rwa [max_eq_left (le_of_lt h_gt)] at this
    obtain ⟨hDxz_ne, hmax_eq⟩ := max_dxz a₁ ha₁_Dxz ha₁_max
    have hSD_chain : coverageSymmDiff x z (Dxz.max' hDxz_ne) = coverageSymmDiff x y a₁ := by
      rw [congr_arg (coverageSymmDiff x z) hmax_eq]
      simp only [coverageSymmDiff, hyz_eq]
    have hCS_chain : coverageSet x (Dxz.max' hDxz_ne) = coverageSet x a₁ :=
      congr_arg (coverageSet x) hmax_eq
    have hSD_ne : (coverageSymmDiff x z (Dxz.max' hDxz_ne)).Nonempty := hSD_chain ▸ hSD1_ne
    refine ⟨hDxz_ne, hSD_ne, ?_⟩
    rw [Finset.min'_of_eq hSD_chain hSD_ne hSD1_ne, hCS_chain]
    exact hv1

theorem QPROT_satisfies_T {n : ℕ} : Ax_T (@QPROT n) := by
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
        have ha_eq : (differingThresholds y x).max' hne2 =
            (differingThresholds x y).max' hne1 :=
          Finset.max'_of_eq (differingThresholds_comm y x) hne2 hne1
        have hD_eq : coverageSymmDiff y x ((differingThresholds y x).max' hne2) =
            coverageSymmDiff x y ((differingThresholds x y).max' hne1) := by
          rw [ha_eq]; exact coverageSymmDiff_comm y x _
        have hD2' : (coverageSymmDiff x y ((differingThresholds x y).max' hne1)).Nonempty :=
          hD_eq ▸ hD2
        have hr_eq := Finset.min'_of_eq hD_eq hD2 hD1
        rw [hr_eq, ha_eq] at hr2
        have hr_mem := Finset.min'_mem _ hD1
        unfold coverageSymmDiff at hr_mem
        rw [Finset.mem_symmDiff] at hr_mem
        rcases hr_mem with ⟨_, hny⟩ | ⟨_, hnx⟩
        · exact hny hr2
        · exact hnx hr1
      · exact Or.inr (qprot_strict_trans x y z hxz hxy_s hyz_s)

theorem QPROT_satisfies_PD {n : ℕ} : Ax_PD (@QPROT n) := by
  intro x y hge hstrict
  have hne : x ≠ y := by
    intro h; obtain ⟨j, hj⟩ := hstrict; rw [h] at hj; linarith
  constructor
  · right
    have hne_dt := differingThresholds_nonempty x y hne
    have ha_ne := (Finset.mem_filter.mp (Finset.max'_mem _ hne_dt)).2
    have hD := symmDiff_nonempty_of_ne x y _ ha_ne
    refine ⟨hne_dt, hD, ?_⟩
    have hr := Finset.min'_mem _ hD
    unfold coverageSymmDiff at hr
    rw [Finset.mem_symmDiff] at hr
    rcases hr with ⟨hx, _⟩ | ⟨hy, hx⟩
    · exact hx
    · exfalso; apply hx; rw [mem_coverageSet] at hy ⊢; exact le_trans hy (hge _)
  · intro hyx
    rcases hyx with rfl | ⟨hne_yx, hD_yx, hr_yx⟩
    · obtain ⟨j, hj⟩ := hstrict; linarith [hge j]
    · have hr := Finset.min'_mem _ hD_yx
      unfold coverageSymmDiff at hr
      rw [Finset.mem_symmDiff] at hr
      rcases hr with ⟨hy_in, hx_out⟩ | ⟨hx_in, hy_out⟩
      · exact hx_out (by rw [mem_coverageSet] at hy_in ⊢; exact le_trans hy_in (hge _))
      · exact hy_out hr_yx

theorem QPROT_satisfies_NDTC {n : ℕ} : Ax_NDTC (@QPROT n) := by
  intro x y _hxy hne hD hr_in_x
  have hqprot_xy : QPROT_strict x y := ⟨hne, hD, hr_in_x⟩
  intro ⟨_, hnotRxy⟩
  exact hnotRxy (Or.inr hqprot_xy)

/-! ## Reverse: C + T + PD + NDTC ⟹ R = Q-PROT -/

/-- Step 1: NDTC + C give weak preference when min(D) ∈ H_{a*}(x). -/
private theorem ndtc_weak {n : ℕ} {R : PrefRel n}
    (hC : Ax_C R) (hNDTC : Ax_NDTC R)
    (x y : Vec n) (hne_xy : x ≠ y)
    (hne : (differingThresholds x y).Nonempty)
    (hD : (coverageSymmDiff x y ((differingThresholds x y).max' hne)).Nonempty)
    (hr : (coverageSymmDiff x y ((differingThresholds x y).max' hne)).min' hD ∈
      coverageSet x ((differingThresholds x y).max' hne)) :
    R x y := by
  have h_not_yx := hNDTC x y hne_xy hne hD hr
  rcases hC x y with h | h
  · exact h
  · by_contra hnotRxy; exact h_not_yx ⟨h, hnotRxy⟩

/-- Technical lemma: r* is in H_{a*}(x) but not in H_{a*}(y). -/
private theorem rstar_in_x_not_y_max {n : ℕ} (x y : Vec n)
    (hne : (differingThresholds x y).Nonempty)
    (hD : (coverageSymmDiff x y ((differingThresholds x y).max' hne)).Nonempty)
    (hr : (coverageSymmDiff x y ((differingThresholds x y).max' hne)).min' hD ∈
      coverageSet x ((differingThresholds x y).max' hne)) :
    (coverageSymmDiff x y ((differingThresholds x y).max' hne)).min' hD ∉
      coverageSet y ((differingThresholds x y).max' hne) := by
  set a_star := (differingThresholds x y).max' hne
  set r_star := (coverageSymmDiff x y a_star).min' hD
  have hr_mem := Finset.min'_mem _ hD
  unfold coverageSymmDiff at hr_mem
  rw [Finset.mem_symmDiff] at hr_mem
  rcases hr_mem with ⟨_, hny⟩ | ⟨hy, hnx⟩
  · exact hny
  · exfalso; exact hnx hr

/-- Step 2: The perturbation argument upgrades weak to strict preference.
    For NDTC, we increase y_{r*} by ε < a* - y_{r*}. Since NDTC checks
    coverage agreement above a*, and the new threshold is below a*,
    NDTC applies cleanly to the perturbed pair. -/
private theorem ndtc_strict {n : ℕ} {R : PrefRel n}
    (hC : Ax_C R) (hT : Ax_T R) (hPD : Ax_PD R) (hNDTC : Ax_NDTC R)
    (x y : Vec n) (hne_xy : x ≠ y)
    (hne : (differingThresholds x y).Nonempty)
    (hD : (coverageSymmDiff x y ((differingThresholds x y).max' hne)).Nonempty)
    (hr : (coverageSymmDiff x y ((differingThresholds x y).max' hne)).min' hD ∈
      coverageSet x ((differingThresholds x y).max' hne)) :
    strictPart R x y := by
  have hRxy := ndtc_weak hC hNDTC x y hne_xy hne hD hr
  constructor
  · exact hRxy
  · intro hRyx
    -- Setup: names for a*, r*
    set a_star := (differingThresholds x y).max' hne
    set r_star := (coverageSymmDiff x y a_star).min' hD
    -- r* ∈ H_{a*}(x) \ H_{a*}(y)
    have hxr_ge : x r_star ≥ a_star := (mem_coverageSet x a_star r_star).mp hr
    have hr_not_y := rstar_in_x_not_y_max x y hne hD hr
    have hyr_lt : y r_star < a_star := by
      rw [mem_coverageSet] at hr_not_y; push_neg at hr_not_y; exact hr_not_y
    -- Choose ε ∈ (0, a* - y_{r*})
    set ε := (a_star - y r_star) / 2 with hε_def
    have hε_pos : ε > 0 := by linarith
    have hε_lt : y r_star + ε < a_star := by linarith
    -- Construct y_eps: increase y_{r*} by ε
    set y_eps : Vec n := fun i => if i = r_star then y i + ε else y i with hy_eps_def
    -- y_eps Pareto-dominates y
    have hge : ∀ i : Fin n, y_eps i ≥ y i := by
      intro i; simp only [hy_eps_def]; split <;> linarith
    have hstrict_at_r : y_eps r_star > y r_star := by
      simp only [hy_eps_def, if_pos rfl]; linarith
    -- PD: y_eps ≻ y
    have hPD_ye : strictPart R y_eps y := hPD y_eps y hge ⟨r_star, hstrict_at_r⟩
    -- T: y_eps ≻ x
    have hR_ye_x : R y_eps x := hT y_eps y x hPD_ye.1 hRyx
    have hnot_x_ye : ¬ R x y_eps := fun h => hPD_ye.2 (hT y x y_eps hRyx h)
    have hstrict_ye_x : strictPart R y_eps x := ⟨hR_ye_x, hnot_x_ye⟩
    -- x ≠ y_eps
    have hne_xye : x ≠ y_eps := by
      intro h; have := congr_fun h r_star
      simp only [hy_eps_def, if_pos rfl] at this; linarith
    -- Coverage at a* for y_eps equals that for y (since y_{r*} + ε < a*)
    have hcov_astar : coverageSet y_eps a_star = coverageSet y a_star := by
      ext i; simp only [coverageSet, Finset.mem_filter, Finset.mem_univ, true_and, hy_eps_def]
      constructor
      · intro hi
        split_ifs at hi with h
        · subst h; linarith
        · exact hi
      · intro hi
        split_ifs with h
        · subst h; linarith
        · exact hi
    -- Coverage above a* for (x, y_eps) agrees: for b > a*, H_b(y_eps) = H_b(y) = H_b(x)
    -- because a* is max differing threshold and y_eps only changes below a*.
    have hcov_above : ∀ b ∈ thresholdValues x y_eps, b > a_star →
        coverageSet x b = coverageSet y_eps b := by
      intro b hb hb_gt
      -- b ∈ thresholdValues(x, y_eps). Show H_b(x) = H_b(y) and H_b(y_eps) = H_b(y).
      -- First: b is either a value of x or a value of y_eps.
      -- Values of y_eps: for i ≠ r*, y_eps_i = y_i. For i = r*, y_eps_{r*} = y_{r*}+ε < a* < b.
      -- If b = y_eps_i, either b = y_i (i ≠ r*) or b = y_{r*}+ε < b (impossible).
      -- Hence b ∈ image(x) ∪ image(y) = thresholdValues(x, y).
      have hb_in_T : b ∈ thresholdValues x y := by
        simp only [thresholdValues, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
          true_and] at hb ⊢
        rcases hb with ⟨i, hi⟩ | ⟨i, hi⟩
        · exact Or.inl ⟨i, hi⟩
        · simp only [hy_eps_def] at hi
          split_ifs at hi with h
          · subst h; linarith  -- b = y_{r*} + ε < a* < b, contradiction
          · exact Or.inr ⟨i, hi⟩
      -- b ∈ T with b > a* = max differing threshold, so coverage agrees
      have hb_agree : coverageSet x b = coverageSet y b := by
        by_contra hne_b
        have hb_diff : b ∈ differingThresholds x y :=
          Finset.mem_filter.mpr ⟨hb_in_T, hne_b⟩
        linarith [Finset.le_max' _ b hb_diff]
      -- H_b(y_eps) = H_b(y) since b > a* > y_{r*} + ε
      have hcov_ye_y : coverageSet y_eps b = coverageSet y b := by
        ext i; simp only [coverageSet, Finset.mem_filter, Finset.mem_univ, true_and, hy_eps_def]
        split_ifs with h
        · subst h; constructor
          · intro hi; linarith
          · intro hi; linarith
        · exact Iff.rfl
      rw [hb_agree, hcov_ye_y]
    -- a* is a differing threshold for (x, y_eps)
    have hcov_ne : coverageSet x a_star ≠ coverageSet y_eps a_star := by
      rw [hcov_astar]
      exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
    -- a* ∈ thresholdValues(x, y_eps)
    have hastar_in_tv : a_star ∈ thresholdValues x y_eps := by
      -- a* ∈ thresholdValues(x, y), so a* is a value of some x_i or y_i
      have hastar_in_T := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).1
      simp only [thresholdValues, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
        true_and] at hastar_in_T ⊢
      rcases hastar_in_T with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact Or.inl ⟨i, hi⟩
      · right; refine ⟨i, ?_⟩
        simp only [hy_eps_def]
        split_ifs with h
        · subst h; linarith  -- y_{r*} = a*, contradicts y_{r*} < a*
        · exact hi
    have hastar_diff : a_star ∈ differingThresholds x y_eps :=
      Finset.mem_filter.mpr ⟨hastar_in_tv, hcov_ne⟩
    -- a* is the MAX differing threshold for (x, y_eps)
    have hastar_max : ∀ b ∈ differingThresholds x y_eps, b ≤ a_star := by
      intro b hb
      by_contra hlt; push_neg at hlt
      obtain ⟨hb_tv, hb_ne⟩ := Finset.mem_filter.mp hb
      exact hb_ne (hcov_above b hb_tv hlt)
    -- Assemble NDTC application on (x, y_eps)
    have hne_dt_xe : (differingThresholds x y_eps).Nonempty := ⟨a_star, hastar_diff⟩
    have hmax_eq : (differingThresholds x y_eps).max' hne_dt_xe = a_star :=
      le_antisymm (hastar_max _ (Finset.max'_mem _ hne_dt_xe)) (Finset.le_max' _ a_star hastar_diff)
    -- Symm diff at a* for (x, y_eps) = symm diff at a* for (x, y)
    have hD_eq : coverageSymmDiff x y_eps a_star = coverageSymmDiff x y a_star := by
      simp only [coverageSymmDiff]; rw [hcov_astar]
    have hD_xe : (coverageSymmDiff x y_eps
        ((differingThresholds x y_eps).max' hne_dt_xe)).Nonempty := by
      rw [hmax_eq]; exact hD_eq ▸ hD
    have hr_xe : (coverageSymmDiff x y_eps
        ((differingThresholds x y_eps).max' hne_dt_xe)).min' hD_xe ∈
        coverageSet x ((differingThresholds x y_eps).max' hne_dt_xe) := by
      have h1 : coverageSymmDiff x y_eps
          ((differingThresholds x y_eps).max' hne_dt_xe) =
          coverageSymmDiff x y a_star := by rw [hmax_eq]; exact hD_eq
      have h2 : (coverageSymmDiff x y_eps
          ((differingThresholds x y_eps).max' hne_dt_xe)).min' hD_xe = r_star :=
        Finset.min'_of_eq h1 hD_xe hD
      rw [h2, hmax_eq]; exact hr
    exact hNDTC x y_eps hne_xye hne_dt_xe hD_xe hr_xe hstrict_ye_x

theorem C_T_PD_NDTC_imp_QPROT {n : ℕ} {R : PrefRel n}
    (hC : Ax_C R) (hT : Ax_T R) (hPD : Ax_PD R) (hNDTC : Ax_NDTC R) :
    ∀ x y, R x y ↔ QPROT x y := by
  intro x y
  constructor
  · -- R x y → QPROT x y
    intro hRxy
    by_cases heq : x = y
    · exact Or.inl heq
    · have hne := differingThresholds_nonempty x y heq
      have ha_ne := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
      have hD := symmDiff_nonempty_of_ne x y _ ha_ne
      have hr_mem := Finset.min'_mem _ hD
      unfold coverageSymmDiff at hr_mem
      rw [Finset.mem_symmDiff] at hr_mem
      rcases hr_mem with ⟨hx, _⟩ | ⟨hy, _⟩
      · exact Or.inr ⟨hne, hD, hx⟩
      · exfalso
        have hne_yx : y ≠ x := fun h => heq h.symm
        have hne_dt_yx : (differingThresholds y x).Nonempty := by
          rw [differingThresholds_comm]; exact hne
        have ha_eq : (differingThresholds y x).max' hne_dt_yx =
            (differingThresholds x y).max' hne :=
          Finset.max'_of_eq (differingThresholds_comm y x) hne_dt_yx hne
        have hD_eq : coverageSymmDiff y x ((differingThresholds y x).max' hne_dt_yx) =
            coverageSymmDiff x y ((differingThresholds x y).max' hne) := by
          rw [ha_eq]; exact coverageSymmDiff_comm y x _
        have hD_yx : (coverageSymmDiff y x ((differingThresholds y x).max' hne_dt_yx)).Nonempty :=
          hD_eq ▸ hD
        have hr_eq := Finset.min'_of_eq hD_eq hD_yx hD
        have hy_in : (coverageSymmDiff y x ((differingThresholds y x).max' hne_dt_yx)).min' hD_yx ∈
            coverageSet y ((differingThresholds y x).max' hne_dt_yx) := by
          rw [hr_eq, ha_eq]; exact hy
        exact (ndtc_strict hC hT hPD hNDTC y x hne_yx hne_dt_yx hD_yx hy_in).2 hRxy
  · -- QPROT x y → R x y
    intro hQPROT
    rcases hQPROT with rfl | ⟨hne_dt, hD, hr⟩
    · rcases hC x x with h | h <;> exact h
    · have hne_xy : x ≠ y := by
        intro h; subst h
        have := Finset.max'_mem _ hne_dt
        simp [differingThresholds] at this
      exact (ndtc_strict hC hT hPD hNDTC x y hne_xy hne_dt hD hr).1

/-! ## Main characterization -/

/-- **Theorem 6'**: A preference is Q-PROT iff it satisfies C, T, PD, and NDTC. -/
theorem QPROT_NDTC_characterization {n : ℕ} {R : PrefRel n} :
    (∀ x y, R x y ↔ QPROT x y) ↔ (Ax_C R ∧ Ax_T R ∧ Ax_PD R ∧ Ax_NDTC R) := by
  constructor
  · intro hR
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Completeness
      intro x y
      rcases QPROT_satisfies_C x y with h | h
      · exact Or.inl ((hR x y).mpr h)
      · exact Or.inr ((hR y x).mpr h)
    · -- Transitivity
      intro x y z hxy hyz
      exact (hR x z).mpr (QPROT_satisfies_T x y z ((hR x y).mp hxy) ((hR y z).mp hyz))
    · -- Pareto Dominance
      intro x y hge hstrict
      have h := QPROT_satisfies_PD x y hge hstrict
      exact ⟨(hR x y).mpr h.1, fun hR' => h.2 ((hR y x).mp hR')⟩
    · -- NDTC
      intro x y hxy hne hD hr hstrict
      have hstrict_qprot : strictPart QPROT y x :=
        ⟨(hR y x).mp hstrict.1, fun h => hstrict.2 ((hR x y).mpr h)⟩
      exact QPROT_satisfies_NDTC x y hxy hne hD hr hstrict_qprot
  · rintro ⟨hC, hT, hPD, hNDTC⟩
    exact C_T_PD_NDTC_imp_QPROT hC hT hPD hNDTC
