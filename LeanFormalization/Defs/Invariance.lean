/-
  PriorityRanking.Defs.Invariance
  Ordinal Invariance (OI) and Prefix-Sum Ordinality (PSO) definitions.

  Paper reference: Section 6.2 (Definitions 10-11)
-/

import LeanFormalization.Basic

/-! ## Ordinal Invariance (Definition 10) -/

/-- A ranking satisfies Ordinal Invariance if applying any strictly increasing
    transformation φ : ℝ → ℝ to all coordinates preserves the ranking. -/
def OrdinalInvariance {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ (φ : ℝ → ℝ), StrictMono φ →
    ∀ (x y : Vec n), R x y ↔ R (φ ∘ x) (φ ∘ y)

/-! ## Prefix-Sum Ordinality (Definition 11) -/

/-- The sign pattern of prefix-sum differences. Two pairs (x,y) and (x',y') have
    the same prefix-sum sign pattern if sgn(S_j(x) - S_j(y)) = sgn(S_j(x') - S_j(y'))
    for all j. -/
def samePrefixSumSignPattern {n : ℕ} (x y x' y' : Vec n) : Prop :=
  ∀ j : Fin n,
    (prefixSum x j > prefixSum y j ↔ prefixSum x' j > prefixSum y' j) ∧
    (prefixSum x j = prefixSum y j ↔ prefixSum x' j = prefixSum y' j) ∧
    (prefixSum x j < prefixSum y j ↔ prefixSum x' j < prefixSum y' j)

/-- A ranking satisfies Prefix-Sum Ordinality if pairs with the same prefix-sum
    sign pattern receive the same ranking. -/
def PrefixSumOrdinality {n : ℕ} (R : PrefRel n) : Prop :=
  ∀ (x y x' y' : Vec n),
    samePrefixSumSignPattern x y x' y' →
    (R x y ↔ R x' y')
