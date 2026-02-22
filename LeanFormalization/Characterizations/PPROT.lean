/-
  PriorityRanking.Characterizations.PPROT
  Theorem 5: P-PROT is characterized by C + LTSF.

  A preference ≿ on X is P-PROT if and only if it satisfies C and LTSF.
  T, PD, CX, CST, CVG are all redundant.
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms

open Finset

/-! ## Helper lemmas for threshold symmetry -/

theorem differingThresholds_comm {n : ℕ} (x y : Vec n) :
    differingThresholds y x = differingThresholds x y := by
  ext a
  simp only [differingThresholds, thresholdValues, Finset.mem_filter,
    Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro ⟨h1, h2⟩; exact ⟨by tauto, Ne.symm h2⟩
  · intro ⟨h1, h2⟩; exact ⟨by tauto, Ne.symm h2⟩

theorem coverageSymmDiff_comm {n : ℕ} (x y : Vec n) (a : ℝ) :
    coverageSymmDiff y x a = coverageSymmDiff x y a := by
  simp only [coverageSymmDiff]
  exact symmDiff_comm _ _

/-! ## Forward: P-PROT satisfies C -/

/-- For x ≠ y with r* ∈ H_{a*}(y), construct PPROT_strict y x. -/
private theorem pprot_strict_of_mem_y {n : ℕ} (x y : Vec n)
    (hne : (differingThresholds x y).Nonempty)
    (hD : (coverageSymmDiff x y ((differingThresholds x y).min' hne)).Nonempty)
    (hy : (coverageSymmDiff x y ((differingThresholds x y).min' hne)).min' hD ∈
      coverageSet y ((differingThresholds x y).min' hne)) :
    PPROT_strict y x := by
  -- Build nonemptiness for (y,x) versions
  have hne_yx : (differingThresholds y x).Nonempty := by
    rw [differingThresholds_comm]; exact hne
  -- a*_yx = a*_xy
  have ha_eq : (differingThresholds y x).min' hne_yx =
      (differingThresholds x y).min' hne :=
    Finset.min'_of_eq (differingThresholds_comm x y) hne_yx hne
  -- D_yx = D_xy
  have hD_eq : coverageSymmDiff y x ((differingThresholds y x).min' hne_yx) =
      coverageSymmDiff x y ((differingThresholds x y).min' hne) := by
    rw [ha_eq]; exact coverageSymmDiff_comm x y _
  have hD_yx : (coverageSymmDiff y x ((differingThresholds y x).min' hne_yx)).Nonempty :=
    hD_eq ▸ hD
  -- r*_yx = r*_xy
  have hr_eq := Finset.min'_of_eq hD_eq hD_yx hD
  -- Construct PPROT_strict y x
  refine ⟨hne_yx, hD_yx, ?_⟩
  rw [hr_eq, ha_eq]
  exact hy

theorem PPROT_satisfies_C {n : ℕ} : Ax_C (@PPROT n) := by
  intro x y
  by_cases hxy : x = y
  · exact Or.inl (hxy ▸ PPROT_refl x)
  · have hne := differingThresholds_nonempty x y hxy
    have ha_ne := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
    have hD := symmDiff_nonempty_of_ne x y _ ha_ne
    have hr_mem := Finset.min'_mem _ hD
    unfold coverageSymmDiff at hr_mem
    rw [Finset.mem_symmDiff] at hr_mem
    rcases hr_mem with ⟨hx, _⟩ | ⟨hy, _⟩
    · left; right; exact ⟨hne, hD, hx⟩
    · right; right; exact pprot_strict_of_mem_y x y hne hD hy

/-! ## Forward: P-PROT satisfies LTSF -/

theorem PPROT_satisfies_LTSF {n : ℕ} : Ax_LTSF (@PPROT n) := by
  intro x y hxy hne hD
  constructor
  · -- PPROT x y → r* ∈ H_{a*}(x)
    rintro (rfl | ⟨_, _, hr⟩)
    · exact absurd rfl hxy
    · exact hr
  · -- r* ∈ H_{a*}(x) → PPROT x y
    intro hr
    exact Or.inr ⟨hne, hD, hr⟩

/-! ## Reverse: C + LTSF implies P-PROT -/

theorem C_LTSF_imp_PPROT {n : ℕ} (R : PrefRel n)
    (hC : Ax_C R) (hLTSF : Ax_LTSF R) :
    ∀ x y, R x y ↔ PPROT x y := by
  intro x y
  by_cases hxy : x = y
  · subst hxy
    exact ⟨fun _ => PPROT_refl x, fun _ => (hC x x).elim id id⟩
  · have hne := differingThresholds_nonempty x y hxy
    have ha_ne := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
    have hD := symmDiff_nonempty_of_ne x y _ ha_ne
    have hltsf := hLTSF x y hxy hne hD
    constructor
    · intro hRxy; exact Or.inr ⟨hne, hD, hltsf.mp hRxy⟩
    · rintro (rfl | ⟨_, _, hr⟩)
      · exact absurd rfl hxy
      · exact hltsf.mpr hr

/-! ## Characterization theorem -/

/-- **Theorem 5**: A preference is P-PROT iff it satisfies C and LTSF. -/
theorem PPROT_characterization {n : ℕ} (R : PrefRel n) :
    (∀ x y, R x y ↔ PPROT x y) ↔ (Ax_C R ∧ Ax_LTSF R) := by
  constructor
  · intro hR
    refine ⟨?_, ?_⟩
    · -- C
      intro x y
      rcases PPROT_satisfies_C x y with h | h
      · exact Or.inl ((hR x y).mpr h)
      · exact Or.inr ((hR y x).mpr h)
    · -- LTSF
      intro x y hxy hne hD
      have hltsf := PPROT_satisfies_LTSF x y hxy hne hD
      constructor
      · intro hRxy; exact hltsf.mp ((hR x y).mp hRxy)
      · intro hr; exact (hR x y).mpr (hltsf.mpr hr)
  · intro ⟨hC, hLTSF⟩
    exact C_LTSF_imp_PPROT R hC hLTSF
