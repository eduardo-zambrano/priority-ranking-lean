# Lean 4 Formalization Plan: "Axiomatizations of Priority-Based Ranking Rules"

## Context

The paper `axiomatization_paper.tex` (21 pages) axiomatizes six priority-based ranking rules on $\mathbb{R}^n_{\geq 0}$ (some extending to all of $\mathbb{R}^n$). A complete Lean 4 formalization would:
- Provide machine-checked verification of all 6 characterization theorems, 3 impossibility theorems, 9 structural propositions, 6 independence results, redundancy results, and the full 14x6 axiom satisfaction table (~84 lemmas)
- Strengthen the paper for JET submission by providing an independently verified formal companion
- Create a reusable library for priority-ordered decision theory

---

## 1. Project Setup

Create a new Lean 4 + Mathlib project:

```bash
# In the PCL project directory
lake +leanprover-toolchain-v4.24.0 new lean_formalization math
cd lean_formalization
lake exe cache get   # download precompiled Mathlib (~30 min saved)
lake build           # verify setup
```

**Key Mathlib imports**: `Order.PiLex`, `Data.Fin.Basic`, `Data.Finset.Basic`, `Data.Finset.Sum`, `Data.Finset.Lattice`, `Data.Real.Basic`, `Tactic`

---

## 2. Module Structure

```
lean_formalization/
  PriorityRanking.lean                    -- root import
  PriorityRanking/
    Basic.lean                             -- Core types, prefixSum, coverageSet
    Defs/
      Rules.lean                           -- PMM, PLS, TMM, TLS, P-PROT, Q-PROT
      Axioms.lean                          -- All 16 axiom predicates
      FOSD.lean                            -- FOSD definition
      Invariance.lean                      -- OI, PSO, EI
    Satisfaction/
      PMM.lean  PLS.lean  TMM.lean         -- Which axioms each rule satisfies
      TLS.lean  PPROT.lean  QPROT.lean     -- (14 lemmas per file, ~84 total)
    Characterizations/
      PMM.lean                             -- Thm 1: PMM = TSM + TSI
      PLS.lean                             -- Thm 2: PLS = C+T+PD+NCA  [HARDEST]
      TMM.lean                             -- Thm 3: TMM = TM + TI
      TLS.lean                             -- Thm 4: TLS = C+TM+GUT    [MEDIUM]
      PPROT.lean                           -- Thm 5: P-PROT = C+LTSF
      QPROT.lean                           -- Thm 6: Q-PROT = C+HTSF
    Impossibility/
      NCA_TM.lean                          -- NCA /\ TM -> False
      FOSD_Threshold.lean                  -- FOSD-mono /\ LTSF/HTSF -> False
      NCA_EI.lean                          -- C+T+PD+NCA+EI -> False
      NoFiniteCompensation.lean            -- C+T+PD+NCA => no finite compensation
    Structural/
      Refinement.lean                      -- PLS refines PMM; TLS refines TMM
      Collapse.lean                        -- PCL=PLS, 12->6 equivalences
      FOSDClassification.lean              -- FOSD-monotonicity classification
      Incomparability.lean                 -- P-PROT vs PLS, P-PROT vs Q-PROT
      Agreements.lean                      -- Universal agreements
      DomainSeparation.lean                -- OI/PSO characterization
    Independence/
      PMM.lean  PLS.lean  TMM.lean         -- Independence of axiom sets
      TLS.lean  PPROT.lean  QPROT.lean
    Redundancy/
      PMM.lean  TMM.lean  TLS.lean         -- Implied axioms (C,T redundant etc.)
      PPROT.lean  QPROT.lean
```

**Total: ~33 Lean files**

---

## 3. Core Type Design

### 3.1 Vectors and Preference Relations

```lean
abbrev Vec (n : Nat) := Fin n -> Real
def NNVec (n : Nat) := { v : Vec n // forall i, 0 <= v i }
def PrefRel (n : Nat) := Vec n -> Vec n -> Prop

def strictPart (R : PrefRel n) (x y : Vec n) : Prop := R x y /\ not (R y x)
def indiffPart (R : PrefRel n) (x y : Vec n) : Prop := R x y /\ R y x
```

### 3.2 Prefix Sums and Coverage Sets

```lean
noncomputable def prefixSum (x : Vec n) (j : Fin n) : Real :=
  Finset.sum (Finset.Iic j) (fun i => x i)

noncomputable def totalSum (x : Vec n) : Real := Finset.sum Finset.univ (fun i => x i)

noncomputable def coverageSet (x : Vec n) (a : Real) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a <= x i)
```

### 3.3 Six Rules (key definitions)

- **PMM/TMM**: Direct comparison of `x 0` / `totalSum x` (trivial)
- **PLS**: Use `Pi.Lex (. < .) (fun _ => (. < .))` from Mathlib -- PLS strict is `Pi.Lex ... y x`
- **TLS**: `Pi.Lex (. > .) (fun _ => (. < .))` on prefix-sum vectors (reverse-index lex)
- **P-PROT/Q-PROT**: Most complex -- require `differingThresholds`, `Finset.min'`/`max'`, `symmDiff`, with nonemptiness proofs at each step

### 3.4 Axioms (16 predicates on `PrefRel n`)

Each is a `Prop`-valued predicate. Examples:
- `Ax_C R := forall x y, R x y \/ R y x`
- `Ax_NCA R := forall x y k, (forall i, i < k -> x i = y i) -> x k > y k -> forall y', (forall i, i <= k -> y' i = y i) -> not (strictPart R y' x)`

**Note**: All definitions involving `Real` will be `noncomputable`. This is standard for proposition-proving (not computation).

**Indexing**: Paper uses 1-based (state 1 = highest priority); Lean uses 0-based (`Fin n` starts at 0). We use 0-based throughout.

---

## 4. Build Order (Sprint Plan)

### Sprint 1: Foundations (Week 1-2)
| Task | File | LOC | Difficulty |
|------|------|-----|-----------|
| Project setup + Mathlib | `lakefile.lean` | 20 | Low |
| Core types, prefixSum, coverageSet, helpers | `Basic.lean` | 200-300 | Low-Med |
| Six rule definitions | `Defs/Rules.lean` | 150-250 | Med |
| 16 axiom definitions | `Defs/Axioms.lean` | 200-300 | Low |
| FOSD, OI, PSO, EI definitions | `Defs/FOSD.lean`, `Invariance.lean` | 100 | Low |
| Concrete example tests (Example 3.5) | inline | 50 | Low |

**Key helper lemmas to build early** (in `Basic.lean`):
- `prefixSum_zero`, `prefixSum_succ`, `prefixSum_last`
- `prefixSum_eq_of_coord_eq`: if x_i = y_i for i <= j, then S_j(x) = S_j(y)
- `nonneg_prefixSum_mono`: nonneg vectors have nondecreasing prefix sums
- `differingThresholds_nonempty`: x != y => differing thresholds nonempty
- `symmDiff_nonempty_of_ne`: unequal Finsets have nonempty symmDiff

### Sprint 2: Easy Wins (Week 2-3)
| Task | File | LOC | Difficulty |
|------|------|-----|-----------|
| PMM = TSM + TSI | `Characterizations/PMM.lean` | 40-60 | Low |
| TMM = TM + TI | `Characterizations/TMM.lean` | 40-60 | Low |
| P-PROT = C + LTSF | `Characterizations/PPROT.lean` | 60-100 | Low |
| Q-PROT = C + HTSF | `Characterizations/QPROT.lean` | 60-100 | Low |
| NCA /\ TM -> False | `Impossibility/NCA_TM.lean` | 30-50 | Low |
| FOSD /\ LTSF/HTSF -> False | `Impossibility/FOSD_Threshold.lean` | 50-80 | Low |
| Begin satisfaction table (PMM, TMM columns) | `Satisfaction/PMM.lean`, `TMM.lean` | 200 | Low |

### Sprint 3: Medium Results (Week 3-4)
| Task | File | LOC | Difficulty |
|------|------|-----|-----------|
| **TLS = C + TM + GUT** | `Characterizations/TLS.lean` | 150-250 | **Medium** |
| Refinement: PLS refines PMM, TLS refines TMM | `Structural/Refinement.lean` | 60-80 | Low |
| PCL = PLS equivalence | `Structural/Collapse.lean` | 100-150 | Med |
| 12->6 collapse (including (iii)-(iv)) | `Structural/Collapse.lean` | 150-200 | Med |
| Continue satisfaction table | `Satisfaction/PLS.lean`, etc. | 300 | Low-Med |

**TLS proof strategy**: Case 1 (S_n(x) != S_n(y)) is direct from TM. Case 2 (S_n(x) = S_n(y)): derive x_i = y_i for i > k*+1 and x_{k*+1} < y_{k*+1} from prefix-sum algebra, then apply GUT. Key tactic: `linarith` after unfolding prefix sums via `prefixSum_succ`.

### Sprint 4: The Boss Fight (Week 4-5)
| Task | File | LOC | Difficulty |
|------|------|-----|-----------|
| **PLS = C + T + PD + NCA** | `Characterizations/PLS.lean` | 200-350 | **Hard** |
| NCA + EI -> False (depends on PLS) | `Impossibility/NCA_EI.lean` | 40-60 | Low |
| No finite compensation | `Impossibility/NoFiniteCompensation.lean` | 80-120 | Med |

**PLS proof strategy** (the hardest proof):
- **Forward** (PLS => axioms): 4 separate lemmas, each straightforward
- **Reverse** (axioms => PLS): For x != y with first differing index k where x_k > y_k:
  1. NCA gives not(y succ x), Completeness gives x succeq y
  2. **Strictness by contradiction**: Assume x ~ y. Construct y_eps with (y_eps)_k = y_k + eps for eps in (0, x_k - y_k). PD gives y_eps succ y; transitivity from y succeq x gives y_eps succ x. But NCA forbids this. Contradiction.
  - Key Lean challenge: constructing y_eps := fun i => if i = k then y k + eps else y i and proving componentwise >= with strict at k
  - Use `exists_between` for eps existence

### Sprint 5: Completeness (Week 5-7)
| Task | File | LOC | Difficulty |
|------|------|-----|-----------|
| Finish satisfaction table (all 84 cells) | `Satisfaction/*.lean` | 200 | Low-Med |
| All 6 independence results | `Independence/*.lean` | 300-500 | Low-Med |
| All 5 redundancy results | `Redundancy/*.lean` | 200-350 | Med |
| FOSD classification | `Structural/FOSDClassification.lean` | 80 | Low |
| Incomparability results | `Structural/Incomparability.lean` | 80 | Low |
| Universal agreements | `Structural/Agreements.lean` | 80 | Low |
| Domain separation (OI/PSO) | `Structural/DomainSeparation.lean` | 120 | Med |
| Final cleanup + verification | all | 100 | Low |

---

## 5. Result Inventory (Complete)

| Category | Count | Difficulty Breakdown |
|----------|-------|---------------------|
| Definitions (rules, axioms, FOSD, OI, PSO) | 27 | All low |
| Characterization theorems | 6 | 4 easy, 1 medium (TLS), 1 hard (PLS) |
| Impossibility theorems | 3 | All easy (counterexamples) |
| No-finite-compensation proposition | 1 | Medium |
| Structural propositions | 9 | 7 easy, 2 medium |
| Independence propositions | 6 | Low-medium |
| Redundancy results | 5 | Medium |
| Axiom satisfaction table | 84 cells | ~70 easy, ~14 medium |
| **Total formal statements** | **~141** | |

---

## 6. Estimated Effort

| Component | LOC | Calendar Time |
|-----------|-----|---------------|
| Foundations (Basic + Defs) | 650-950 | 1-2 weeks |
| Satisfaction table | 600-900 | 3-5 days |
| Easy characterizations (4) | 200-360 | 2 days |
| TLS characterization | 150-250 | 2-3 days |
| **PLS characterization** | **200-350** | **3-5 days** |
| Impossibility theorems | 200-310 | 1-2 days |
| Structural propositions | 300-500 | 3-5 days |
| Independence + Redundancy | 500-850 | 4-7 days |
| **Total** | **2,800-4,500** | **5-8 weeks** |

For someone learning Lean 4 concurrently: **10-16 weeks**.

---

## 7. Key Technical Risks and Mitigations

| Risk | Impact | Mitigation |
|------|--------|-----------|
| P-PROT/Q-PROT definitions too verbose | Delays Sprint 1 | Decompose into helper functions; accept 50-100 LOC per definition |
| PLS strictness proof fights type system | Blocks Sprint 4 | Break into ~10 small lemmas; `exists_between` for eps |
| `Finset.Iic` on `Fin n` missing lemmas | Slows prefix-sum proofs | Build 5-6 helper lemmas in `Basic.lean` early |
| Independence constructions (esp. "Drop T") | Low priority | Can use `sorry` initially; not load-bearing |
| `Fin n` arithmetic requires many bounds proofs | Pervasive friction | Heavy use of `omega` tactic; helper lemmas |

---

## 8. Verification Strategy

1. **Concrete tests**: Formalize Example 3.5 (all 6 rules on (3,1,0) vs (2,0,3)) to validate definitions
2. **Cross-checks**: Each characterization theorem cross-validates rule definitions against axiom definitions
3. **`sorry`-free goal**: All files compile with zero `sorry` at completion
4. **CI**: Set up GitHub Actions with `lake build` to catch regressions

---

## 9. Implementation Actions

1. Create `lean_formalization/` directory in the project root
2. Initialize Lake project with Mathlib dependency
3. Implement files in sprint order (Sprints 1-5 above)
4. After each sprint, run `lake build` to verify everything compiles
5. When complete, add a note in the paper's introduction mentioning the formal companion

---

## Appendix A: Detailed Axiom Definitions in Lean 4

```lean
-- Completeness
def Ax_C (R : PrefRel n) : Prop :=
  forall x y, R x y \/ R y x

-- Transitivity
def Ax_T (R : PrefRel n) : Prop :=
  forall x y z, R x y -> R y z -> R x z

-- Pareto Dominance
def Ax_PD (R : PrefRel n) : Prop :=
  forall x y, (forall i, x i >= y i) -> (exists j, x j > y j) -> strictPart R x y

-- Top-State Monotonicity
def Ax_TSM (R : PrefRel n) : Prop :=
  forall x y, x 0 > y 0 -> strictPart R x y

-- Total Monotonicity
def Ax_TM (R : PrefRel n) : Prop :=
  forall x y, totalSum x > totalSum y -> strictPart R x y

-- Top-State Indifference
def Ax_TSI (R : PrefRel n) : Prop :=
  forall x y, x 0 = y 0 -> indiffPart R x y

-- Total Indifference
def Ax_TI (R : PrefRel n) : Prop :=
  forall x y, totalSum x = totalSum y -> indiffPart R x y

-- Coordinate Sure-Thing (CST)
def Ax_CST (R : PrefRel n) : Prop :=
  forall (S : Finset (Fin n)) (x y x' y' : Vec n),
    (forall i, i in S -> x i = y i) ->
    (forall i, i in S -> x' i = y' i) ->
    (forall i, i notin S -> x i = x' i) ->
    (forall i, i notin S -> y i = y' i) ->
    (R x y <-> R x' y')

-- Non-Compensability Across Levels (NCA)
def Ax_NCA (R : PrefRel n) : Prop :=
  forall x y (k : Fin n),
    (forall i, i < k -> x i = y i) ->
    x k > y k ->
    forall y', (forall i, i <= k -> y' i = y i) ->
      not (strictPart R y' x)

-- Convexity (CX)
def Ax_CX (R : PrefRel n) : Prop :=
  forall x y z (lam : Real),
    R x z -> R y z -> 0 < lam -> lam < 1 ->
    R (fun i => lam * x i + (1 - lam) * y i) z

-- Upward Priority Transfer (UPT)
def Ax_UPT (R : PrefRel n) : Prop :=
  forall x y (k : Fin n) (delta : Real),
    delta > 0 ->
    k.val + 1 < n ->
    x k = y k + delta ->
    x (Fin.mk (k.val + 1) (by omega)) = y (Fin.mk (k.val + 1) (by omega)) - delta ->
    (forall i, i != k -> i.val != k.val + 1 -> x i = y i) ->
    totalSum x = totalSum y ->
    strictPart R x y

-- Generalized Upward Transfer (GUT)
def Ax_GUT (R : PrefRel n) : Prop :=
  forall x y (k : Fin n),
    k.val + 1 < n ->
    (forall i, i.val > k.val + 1 -> x i = y i) ->
    x (Fin.mk (k.val + 1) (by omega)) < y (Fin.mk (k.val + 1) (by omega)) ->
    totalSum x = totalSum y ->
    strictPart R x y

-- Coverage-Based Comparison (CVG)
def Ax_CVG (R : PrefRel n) : Prop :=
  forall x y x' y',
    (forall a, coverageSet x a = coverageSet y a <-> coverageSet x' a = coverageSet y' a) ->
    (R x y <-> R x' y')

-- Exchange Invariance (EI)
def Ax_EI (R : PrefRel n) : Prop :=
  forall x (pi : Equiv.Perm (Fin n)),
    indiffPart R x (x circ pi)
```

## Appendix B: Detailed Rule Definitions in Lean 4

```lean
-- PMM: x >= y iff x_0 >= y_0
noncomputable def PMM : PrefRel n :=
  fun x y => x 0 >= y 0

-- PLS: lexicographic on coordinates (state 0 first)
-- PLS_strict x y means x is strictly preferred to y
noncomputable def PLS_strict (x y : Vec n) : Prop :=
  Pi.Lex (. < .) (fun _ => (. < .)) y x

noncomputable def PLS : PrefRel n :=
  fun x y => x = y \/ PLS_strict x y

-- TMM: compare total sums
noncomputable def TMM : PrefRel n :=
  fun x y => totalSum x >= totalSum y

-- TLS: lexicographic on prefix sums from bottom (index n-1 first)
noncomputable def TLS_strict (x y : Vec n) : Prop :=
  Pi.Lex (. > .) (fun _ => (. < .)) (prefixVec y) (prefixVec x)

noncomputable def TLS : PrefRel n :=
  fun x y => x = y \/ TLS_strict x y

-- P-PROT: threshold scanning from lowest
noncomputable def thresholdValues (x y : Vec n) : Finset Real :=
  (Finset.univ.image x) \cup (Finset.univ.image y)

noncomputable def differingThresholds (x y : Vec n) : Finset Real :=
  (thresholdValues x y).filter (fun a => coverageSet x a != coverageSet y a)

-- (Requires nonemptiness proofs for min'/max' calls)
noncomputable def PPROT_strict (x y : Vec n) (hne : x != y) : Prop :=
  let dt := differingThresholds x y
  exists (hdt : dt.Nonempty),
    let a_star := dt.min' hdt
    let D := (coverageSet x a_star).symmDiff (coverageSet y a_star)
    exists (hD : D.Nonempty),
      let r_star := D.min' hD
      r_star in coverageSet x a_star

-- Q-PROT: threshold scanning from highest (same but max' instead of min')
```

## Appendix C: Mathlib Dependencies Map

| Component | Mathlib Module | Purpose |
|-----------|---------------|---------|
| Vector type | `Data.Fin.Basic` | `Fin n -> Real` |
| Lexicographic order | `Order.PiLex` | `Pi.Lex` for PLS, TLS |
| Finite sums | `Data.Finset.Sum` | `Finset.sum` for prefix sums |
| Initial segments | `Order.LocallyFiniteOrder` | `Finset.Iic` for prefix ranges |
| Coverage sets | `Data.Finset.Basic` | `Finset.filter`, `Finset.univ` |
| Symmetric difference | `Order.SymmDiff` | `symmDiff` for P-PROT/Q-PROT |
| Min/max of finsets | `Data.Finset.Lattice` | `Finset.min'`, `Finset.max'` |
| Real arithmetic | `Data.Real.Basic` | `Real` field operations |
| Permutations | `GroupTheory.Perm.Basic` | `Equiv.Perm` for EI axiom |
| Tactics | `Tactic` | `linarith`, `omega`, `ring`, `norm_num`, `simp` |
