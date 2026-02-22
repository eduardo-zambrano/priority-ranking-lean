/-
  PriorityRanking.Characterizations.QPROT
  Theorem 6: Q-PROT is characterized by C + HTSF.

  A preference ≿ on X is Q-PROT if and only if it satisfies C and HTSF.
  T, PD, CX, CST, CVG are all redundant.
-/

import LeanFormalization.Defs.Rules
import LeanFormalization.Defs.Axioms
import LeanFormalization.Characterizations.PPROT  -- for symmetry helpers

open Finset

/-! ## Forward: Q-PROT satisfies C -/

private theorem qprot_strict_of_mem_y {n : ℕ} (x y : Vec n)
    (hne : (differingThresholds x y).Nonempty)
    (hD : (coverageSymmDiff x y ((differingThresholds x y).max' hne)).Nonempty)
    (hy : (coverageSymmDiff x y ((differingThresholds x y).max' hne)).min' hD ∈
      coverageSet y ((differingThresholds x y).max' hne)) :
    QPROT_strict y x := by
  have hne_yx : (differingThresholds y x).Nonempty := by
    rw [differingThresholds_comm]; exact hne
  have ha_eq : (differingThresholds y x).max' hne_yx =
      (differingThresholds x y).max' hne :=
    Finset.max'_of_eq (differingThresholds_comm x y) hne_yx hne
  have hD_eq : coverageSymmDiff y x ((differingThresholds y x).max' hne_yx) =
      coverageSymmDiff x y ((differingThresholds x y).max' hne) := by
    rw [ha_eq]; exact coverageSymmDiff_comm x y _
  have hD_yx : (coverageSymmDiff y x ((differingThresholds y x).max' hne_yx)).Nonempty :=
    hD_eq ▸ hD
  have hr_eq := Finset.min'_of_eq hD_eq hD_yx hD
  refine ⟨hne_yx, hD_yx, ?_⟩
  rw [hr_eq, ha_eq]
  exact hy

theorem QPROT_satisfies_C {n : ℕ} : Ax_C (@QPROT n) := by
  intro x y
  by_cases hxy : x = y
  · exact Or.inl (hxy ▸ QPROT_refl x)
  · have hne := differingThresholds_nonempty x y hxy
    have ha_ne : coverageSet x ((differingThresholds x y).max' hne) ≠
        coverageSet y ((differingThresholds x y).max' hne) :=
      (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
    have hD := symmDiff_nonempty_of_ne x y _ ha_ne
    have hr_mem := Finset.min'_mem _ hD
    unfold coverageSymmDiff at hr_mem
    rw [Finset.mem_symmDiff] at hr_mem
    rcases hr_mem with ⟨hx, _⟩ | ⟨hy, _⟩
    · left; right; exact ⟨hne, hD, hx⟩
    · right; right; exact qprot_strict_of_mem_y x y hne hD hy

/-! ## Forward: Q-PROT satisfies HTSF -/

theorem QPROT_satisfies_HTSF {n : ℕ} : Ax_HTSF (@QPROT n) := by
  intro x y hxy hne hD
  constructor
  · rintro (rfl | ⟨_, _, hr⟩)
    · exact absurd rfl hxy
    · exact hr
  · intro hr
    exact Or.inr ⟨hne, hD, hr⟩

/-! ## Reverse: C + HTSF implies Q-PROT -/

theorem C_HTSF_imp_QPROT {n : ℕ} (R : PrefRel n)
    (hC : Ax_C R) (hHTSF : Ax_HTSF R) :
    ∀ x y, R x y ↔ QPROT x y := by
  intro x y
  by_cases hxy : x = y
  · subst hxy
    exact ⟨fun _ => QPROT_refl x, fun _ => (hC x x).elim id id⟩
  · have hne := differingThresholds_nonempty x y hxy
    have ha_ne := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
    have hD := symmDiff_nonempty_of_ne x y _ ha_ne
    have hhtsf := hHTSF x y hxy hne hD
    constructor
    · intro hRxy; exact Or.inr ⟨hne, hD, hhtsf.mp hRxy⟩
    · rintro (rfl | ⟨_, _, hr⟩)
      · exact absurd rfl hxy
      · exact hhtsf.mpr hr

/-! ## Characterization theorem -/

/-- **Theorem 6**: A preference is Q-PROT iff it satisfies C and HTSF. -/
theorem QPROT_characterization {n : ℕ} (R : PrefRel n) :
    (∀ x y, R x y ↔ QPROT x y) ↔ (Ax_C R ∧ Ax_HTSF R) := by
  constructor
  · intro hR
    refine ⟨?_, ?_⟩
    · intro x y
      rcases QPROT_satisfies_C x y with h | h
      · exact Or.inl ((hR x y).mpr h)
      · exact Or.inr ((hR y x).mpr h)
    · intro x y hxy hne hD
      have hhtsf := QPROT_satisfies_HTSF x y hxy hne hD
      constructor
      · intro hRxy; exact hhtsf.mp ((hR x y).mp hRxy)
      · intro hr; exact (hR x y).mpr (hhtsf.mpr hr)
  · intro ⟨hC, hHTSF⟩
    exact C_HTSF_imp_QPROT R hC hHTSF
