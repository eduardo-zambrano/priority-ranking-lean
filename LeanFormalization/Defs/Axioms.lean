/-
  PriorityRanking.Defs.Axioms
  All 16 axiom definitions as predicates on PrefRel n.

  Paper reference: Section 3 (Axioms 1-16)
-/

import LeanFormalization.Basic

open Finset

/-! ## Order axioms (Section 3.1) -/

/-- Axiom 1: Completeness. For all x, y: x ≿ y or y ≿ x. -/
def Ax_C {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ x y, R x y ∨ R y x

/-- Axiom 2: Transitivity. If x ≿ y and y ≿ z, then x ≿ z. -/
def Ax_T {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ x y z, R x y → R y z → R x z

/-! ## Monotonicity axioms (Section 3.2) -/

/-- Axiom 3: Pareto Dominance. If x ≥ y componentwise with strict somewhere, then x ≻ y. -/
def Ax_PD {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ x y, (∀ i : Fin n, x i ≥ y i) → (∃ j : Fin n, x j > y j) → strictPart R x y

/-- Axiom 4: Top-State Monotonicity. If x₀ > y₀, then x ≻ y. -/
def Ax_TSM {n : ℕ} [NeZero n] (R : PrefRel n) : Prop :=
  ∀ x y, x ⟨0, NeZero.pos n⟩ > y ⟨0, NeZero.pos n⟩ → strictPart R x y

/-- Axiom 5: Total Monotonicity. If S_n(x) > S_n(y), then x ≻ y. -/
def Ax_TM {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ x y, totalSum x > totalSum y → strictPart R x y

/-! ## Indifference axioms (Section 3.3) -/

/-- Axiom 6: Top-State Indifference. If x₀ = y₀, then x ~ y. -/
def Ax_TSI {n : ℕ} [NeZero n] (R : PrefRel n) : Prop :=
  ∀ x y, x ⟨0, NeZero.pos n⟩ = y ⟨0, NeZero.pos n⟩ → indiffPart R x y

/-- Axiom 7: Total Indifference. If S_n(x) = S_n(y), then x ~ y. -/
def Ax_TI {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ x y, totalSum x = totalSum y → indiffPart R x y

/-! ## Separability axioms (Section 3.4) -/

/-- Axiom 8: Coordinate Sure-Thing (CST).
    If x and y agree on a set S of coordinates, then replacing the common values
    on S does not change the ranking. -/
def Ax_CST {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ (S : Finset (Fin n)) (x y x' y' : Vec n),
    (∀ i, i ∈ S → x i = y i) →
    (∀ i, i ∈ S → x' i = y' i) →
    (∀ i, i ∉ S → x i = x' i) →
    (∀ i, i ∉ S → y i = y' i) →
    (R x y ↔ R x' y')

/-- Axiom 9: Non-Compensability Across Levels (NCA).
    If x and y agree on all coordinates above k and x_k > y_k,
    then no y' agreeing with y on coords ≤ k can be strictly preferred to x. -/
def Ax_NCA {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ (x y : Vec n) (k : Fin n),
    (∀ i : Fin n, i < k → x i = y i) →
    x k > y k →
    ∀ y' : Vec n, (∀ i : Fin n, i ≤ k → y' i = y i) →
      ¬ strictPart R y' x

/-! ## Convexity (Section 3.5) -/

/-- Axiom 10: Convexity. Upper contour sets are convex. -/
def Ax_CX {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ (x y z : Vec n) (lam : ℝ),
    R x z → R y z → 0 < lam → lam < 1 →
    R (fun i => lam * x i + (1 - lam) * y i) z

/-! ## Transfer axioms (Section 3.6) -/

/-- Axiom 11: Upward Priority Transfer (UPT).
    Transferring δ > 0 from state k+1 to state k (preserving total) gives a strict improvement. -/
def Ax_UPT {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ (x y : Vec n) (k : Fin n) (δ : ℝ),
    δ > 0 →
    (hk : k.val + 1 < n) →
    x k = y k + δ →
    x ⟨k.val + 1, hk⟩ = y ⟨k.val + 1, hk⟩ - δ →
    (∀ i : Fin n, i ≠ k → i.val ≠ k.val + 1 → x i = y i) →
    (∀ i : Fin n, 0 ≤ x i) →   -- x remains in domain
    strictPart R x y

/-- Axiom 12: Generalized Upward Transfer (GUT).
    If x and y agree on all coordinates after k+1, x_{k+1} < y_{k+1},
    and totals are equal, then x ≻ y.
    (The "mass" shifted from k+1 to higher-priority states.) -/
def Ax_GUT {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ (x y : Vec n) (k : Fin n),
    (hk : k.val + 1 < n) →
    (∀ i : Fin n, i.val > k.val + 1 → x i = y i) →
    x ⟨k.val + 1, hk⟩ < y ⟨k.val + 1, hk⟩ →
    totalSum x = totalSum y →
    strictPart R x y

/-! ## Threshold axioms (Section 3.7) -/

/-- Axiom 14: Lowest Threshold Scanning First (LTSF).
    For distinct x, y: find a* = min threshold where coverage sets differ.
    x ≿ y iff the highest-priority state in the symmetric difference is in H_{a*}(x).
    The biconditional is essential: it says the ranking is *determined* by the
    scanning procedure, not merely consistent with it. -/
def Ax_LTSF {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ (x y : Vec n),
    x ≠ y →
    ∀ (hne : (differingThresholds x y).Nonempty),
      ∀ (hD : (coverageSymmDiff x y ((differingThresholds x y).min' hne)).Nonempty),
        R x y ↔
          (coverageSymmDiff x y ((differingThresholds x y).min' hne)).min' hD ∈
            coverageSet x ((differingThresholds x y).min' hne)

/-- Axiom 15: Highest Threshold Scanning First (HTSF).
    Same as LTSF but uses max threshold. -/
def Ax_HTSF {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ (x y : Vec n),
    x ≠ y →
    ∀ (hne : (differingThresholds x y).Nonempty),
      ∀ (hD : (coverageSymmDiff x y ((differingThresholds x y).max' hne)).Nonempty),
        R x y ↔
          (coverageSymmDiff x y ((differingThresholds x y).max' hne)).min' hD ∈
            coverageSet x ((differingThresholds x y).max' hne)

/-! ## Non-compensation axioms for threshold rules (Section 4.4) -/

/-- Axiom: No Upward Threshold Compensation (NUTC).
    For distinct x, y: let a* = min differing threshold, D = H_{a*}(x) △ H_{a*}(y).
    If min(D) ∈ H_{a*}(x), then ¬(y ≻ x).
    Normative content: a coverage advantage at a low threshold is non-compensable
    by high-threshold differences. -/
def Ax_NUTC {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ (x y : Vec n),
    x ≠ y →
    ∀ (hne : (differingThresholds x y).Nonempty),
      ∀ (hD : (coverageSymmDiff x y ((differingThresholds x y).min' hne)).Nonempty),
        (coverageSymmDiff x y ((differingThresholds x y).min' hne)).min' hD ∈
            coverageSet x ((differingThresholds x y).min' hne) →
          ¬ strictPart R y x

/-- Axiom: No Downward Threshold Compensation (NDTC).
    Same as NUTC but uses max threshold instead of min.
    Normative content: a coverage advantage at a high threshold is non-compensable
    by low-threshold differences. -/
def Ax_NDTC {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ (x y : Vec n),
    x ≠ y →
    ∀ (hne : (differingThresholds x y).Nonempty),
      ∀ (hD : (coverageSymmDiff x y ((differingThresholds x y).max' hne)).Nonempty),
        (coverageSymmDiff x y ((differingThresholds x y).max' hne)).min' hD ∈
            coverageSet x ((differingThresholds x y).max' hne) →
          ¬ strictPart R y x

/-! ## Invariance axioms (Section 3.8) -/

/-- Axiom 16: Exchange Invariance (EI).
    For any permutation π: x ~ π(x).
    Here π(x)_i = x_{π(i)}, i.e., the value at state π(i) is reassigned to state i. -/
def Ax_EI {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ (x : Vec n) (π : Equiv.Perm (Fin n)),
    indiffPart R x (x ∘ π)

/-! ## FOSD-monotonicity (derived axiom) -/

/-- A preference is FOSD-monotone if x FOSD-dominates y implies x ≻ y. -/
def Ax_FOSD_mono {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ x y, fosdStrict x y → strictPart R x y
