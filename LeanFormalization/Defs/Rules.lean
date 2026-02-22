/-
  PriorityRanking.Defs.Rules
  Definitions of the six priority-based ranking rules:
  PMM, PLS, TMM, TLS, P-PROT, Q-PROT.

  Paper reference: Section 2.3 (Definitions 4-9)
-/

import LeanFormalization.Basic
import Mathlib.Order.PiLex

open Finset

/-! ## PMM: Priority Maximin (Definition 4) -/

/-- PMM weak preference: x ≿_PMM y iff x₀ ≥ y₀.
    (Paper: x₁ ≥ y₁ in 1-based indexing.) -/
noncomputable def PMM {n : ℕ} [NeZero n] : PrefRel n :=
  fun x y => x ⟨0, NeZero.pos n⟩ ≥ y ⟨0, NeZero.pos n⟩

/-- PMM strict: x ≻_PMM y iff x₀ > y₀. -/
theorem PMM_strict {n : ℕ} [NeZero n] (x y : Vec n) :
    strictPart PMM x y ↔ x ⟨0, NeZero.pos n⟩ > y ⟨0, NeZero.pos n⟩ := by
  simp only [strictPart, PMM, ge_iff_le, not_le, gt_iff_lt]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; constructor <;> linarith

/-- PMM indifference: x ~_PMM y iff x₀ = y₀. -/
theorem PMM_indiff {n : ℕ} [NeZero n] (x y : Vec n) :
    indiffPart PMM x y ↔ x ⟨0, NeZero.pos n⟩ = y ⟨0, NeZero.pos n⟩ := by
  simp only [indiffPart, PMM, ge_iff_le]
  constructor
  · intro ⟨h1, h2⟩; exact le_antisymm h2 h1
  · intro h; exact ⟨le_of_eq h.symm, le_of_eq h⟩

/-! ## PLS: Priority Lexicographic by States (Definition 5) -/

/-- PLS strict preference: x ≻_PLS y iff at the first coordinate where x and y differ,
    x has the larger value.
    Uses Pi.Lex from Mathlib: Pi.Lex r s a b means ∃ i, (∀ j, r j i → a j = b j) ∧ s i (a i) (b i).
    With r = (· < ·) and s _ = (· < ·), Pi.Lex (· < ·) (· < ·) y x means
    "∃ i, (∀ j < i, y j = x j) ∧ y i < x i", i.e., x is PLS-strictly better than y. -/
noncomputable def PLS_strict {n : ℕ} (x y : Vec n) : Prop :=
  Pi.Lex (· < ·) (· < ·) y x

/-- PLS weak preference: x ≿_PLS y iff x = y or x ≻_PLS y. -/
noncomputable def PLS {n : ℕ} : PrefRel n :=
  fun x y => x = y ∨ PLS_strict x y

/-! ## TMM: Total Mass Maximin (Definition 6) -/

/-- TMM weak preference: x ≿_TMM y iff S_n(x) ≥ S_n(y). -/
noncomputable def TMM {n : ℕ} : PrefRel n :=
  fun x y => totalSum x ≥ totalSum y

/-- TMM strict: x ≻_TMM y iff S_n(x) > S_n(y). -/
theorem TMM_strict {n : ℕ} (x y : Vec n) :
    strictPart TMM x y ↔ totalSum x > totalSum y := by
  simp only [strictPart, TMM, ge_iff_le, not_le, gt_iff_lt]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; constructor <;> linarith

/-! ## TLS: Total-First Lexicographic (Definition 7) -/

/-- TLS strict preference: x ≻_TLS y iff at the last prefix-sum index where S_j(x) ≠ S_j(y),
    S_j(x) > S_j(y).

    This is lexicographic comparison of prefix sums scanning from bottom (largest index first).
    Using Pi.Lex with reversed index order: Pi.Lex (· > ·) (· < ·) on prefix vectors,
    applied as (prefixVec y, prefixVec x).

    Pi.Lex (· > ·) (· < ·) (prefixVec y) (prefixVec x) means:
    ∃ k, (∀ j, j > k → prefixVec y j = prefixVec x j) ∧ prefixVec y k < prefixVec x k
    i.e., ∃ k, (∀ j > k, S_j(x) = S_j(y)) ∧ S_k(x) > S_k(y). -/
noncomputable def TLS_strict {n : ℕ} (x y : Vec n) : Prop :=
  Pi.Lex (· > ·) (· < ·) (prefixVec y) (prefixVec x)

/-- TLS weak preference. -/
noncomputable def TLS {n : ℕ} : PrefRel n :=
  fun x y => x = y ∨ TLS_strict x y

/-! ## P-PROT: Priority-Protective (Definition 8) -/

/-- P-PROT strict preference.
    For x ≠ y: find a* = min threshold in thresholdValues(x,y) where coverage sets differ.
    Let D = symmetric difference of H_{a*}(x) and H_{a*}(y).
    Let r* = min element of D. Then x ≻ y iff r* ∈ H_{a*}(x). -/
noncomputable def PPROT_strict {n : ℕ} (x y : Vec n) : Prop :=
  ∃ (hne : (differingThresholds x y).Nonempty),
    ∃ (hD : (coverageSymmDiff x y ((differingThresholds x y).min' hne)).Nonempty),
      (coverageSymmDiff x y ((differingThresholds x y).min' hne)).min' hD ∈
        coverageSet x ((differingThresholds x y).min' hne)

/-- P-PROT weak preference. -/
noncomputable def PPROT {n : ℕ} : PrefRel n :=
  fun x y => x = y ∨ PPROT_strict x y

/-! ## Q-PROT: Quality-Protective (Definition 9) -/

/-- Q-PROT strict preference.
    Same as P-PROT but uses max threshold instead of min. -/
noncomputable def QPROT_strict {n : ℕ} (x y : Vec n) : Prop :=
  ∃ (hne : (differingThresholds x y).Nonempty),
    ∃ (hD : (coverageSymmDiff x y ((differingThresholds x y).max' hne)).Nonempty),
      (coverageSymmDiff x y ((differingThresholds x y).max' hne)).min' hD ∈
        coverageSet x ((differingThresholds x y).max' hne)

/-- Q-PROT weak preference. -/
noncomputable def QPROT {n : ℕ} : PrefRel n :=
  fun x y => x = y ∨ QPROT_strict x y

/-! ## Basic properties of the rules -/

/-- All six rules are reflexive. -/
theorem PMM_refl {n : ℕ} [NeZero n] (x : Vec n) : PMM x x := le_refl _
theorem PLS_refl {n : ℕ} (x : Vec n) : PLS x x := Or.inl rfl
theorem TMM_refl {n : ℕ} (x : Vec n) : TMM x x := le_refl _
theorem TLS_refl {n : ℕ} (x : Vec n) : TLS x x := Or.inl rfl
theorem PPROT_refl {n : ℕ} (x : Vec n) : PPROT x x := Or.inl rfl
theorem QPROT_refl {n : ℕ} (x : Vec n) : QPROT x x := Or.inl rfl
