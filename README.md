# Lean 4 Formalization: Axiomatizations of Priority-Based Ranking Rules

Formal verification companion to **"Axiomatizations of Priority-Based Ranking Rules"** by Eduardo Zambrano. Built with [Lean 4](https://lean-lang.org/) (v4.28.0) and [Mathlib](https://leanprover-community.github.io/) (v4.28.0).

## Overview

The paper axiomatizes six ranking rules for comparing vectors in $\mathbb{R}^n$ when coordinates have an exogenous priority order (e.g., journal quality tiers, risk categories). This repository contains a complete, sorry-free formalization of all six characterization theorems, three impossibility results, structural relationships, and axiom satisfaction/violation proofs.

**4,800+ lines of Lean 4 &middot; 158 theorems &middot; 0 sorrys**

## Characterization Theorems

Each characterization theorem is an `iff`: the rule equals the conjunction of its axioms.

| Paper | Theorem | Axioms | File |
|-------|---------|--------|------|
| Theorem [PMM] | PMM = TCM ∧ TCI | Top-Coordinate Monotonicity, Top-Coordinate Indifference | [`Characterizations/PMM.lean`](LeanFormalization/Characterizations/PMM.lean) |
| Theorem [PLS] | PLS = C ∧ T ∧ PD ∧ NCA | Completeness, Transitivity, Priority Dominance, Non-Compensatory Advantage | [`Characterizations/PLS.lean`](LeanFormalization/Characterizations/PLS.lean) |
| Theorem [TMM] | TMM = TM ∧ TI | Total Monotonicity, Total Independence | [`Characterizations/TMM.lean`](LeanFormalization/Characterizations/TMM.lean) |
| Theorem [TLS] | TLS = C ∧ TM ∧ GUT | Completeness, Total Monotonicity, Generalized Uniform Transfer | [`Characterizations/TLS.lean`](LeanFormalization/Characterizations/TLS.lean) |
| Theorem [P-PROT] | P-PROT = C ∧ T ∧ PD ∧ NUTC | Completeness, Transitivity, Priority Dominance, No Upward Threshold Compensation | [`Characterizations/PPROT_NUTC.lean`](LeanFormalization/Characterizations/PPROT_NUTC.lean) |
| Theorem [Q-PROT] | Q-PROT = C ∧ T ∧ PD ∧ NDTC | Completeness, Transitivity, Priority Dominance, No Downward Threshold Compensation | [`Characterizations/QPROT_NDTC.lean`](LeanFormalization/Characterizations/QPROT_NDTC.lean) |

> **Naming note.** The Lean code uses `Ax_TSM` / `Ax_TSI` (Top-State Monotonicity / Indifference) where the paper uses TCM / TCI (Top-Coordinate Monotonicity / Indifference). These are identical definitions; the paper's naming was finalized after the formalization was written.

## Additional Results

### Impossibility Theorems

| Paper | Statement | File |
|-------|-----------|------|
| Theorem [NCA ∧ TM incompatible] | NCA ∧ TM → ⊥ | [`Impossibility/NCA_TM.lean`](LeanFormalization/Impossibility/NCA_TM.lean) |
| Theorem [FOSD ∧ threshold non-compensation incompatible] | FOSD ∧ NUTC → ⊥, FOSD ∧ NDTC → ⊥ | [`Impossibility/FOSD_Threshold.lean`](LeanFormalization/Impossibility/FOSD_Threshold.lean) |
| Theorem [NUTC ∧ NDTC cannot be reconciled] | C ∧ T ∧ PD ∧ NUTC ∧ NDTC → ⊥ | [`Impossibility/NUTC_NDTC.lean`](LeanFormalization/Impossibility/NUTC_NDTC.lean) |

> The file also proves the stronger intermediate result that FOSD is incompatible with LTSF and HTSF (the biconditional threshold-scanning axioms).

### Structural Results
- **PLS refines PMM** and **TLS refines TMM** ([`Structural/Refinement.lean`](LeanFormalization/Structural/Refinement.lean))
- **PCL = PLS**: The prefix-sum lexicographic rule equals PLS on all of $\mathbb{R}^n$ ([`Structural/Refinement.lean`](LeanFormalization/Structural/Refinement.lean))

### Axiom Satisfaction and Violation

Each rule is verified against all relevant axioms. These correspond to the paper's axiom satisfaction tables (Section 3 and Appendix B).

| Rule | File | Satisfies | Violates |
|------|------|-----------|----------|
| PMM | [`Satisfaction/PMM.lean`](LeanFormalization/Satisfaction/PMM.lean) | C, T, TCM, TCI, NCA, CST, CX | PD |
| TMM | [`Satisfaction/TMM.lean`](LeanFormalization/Satisfaction/TMM.lean) | C, T, TM, TI, PD, CST, CX, EI | TCM |
| PLS | [`Satisfaction/PLS.lean`](LeanFormalization/Satisfaction/PLS.lean) | C, T, PD, NCA, TCM, UPT, CST, CX | TM, TI, TCI, GUT, EI |
| TLS | [`Satisfaction/TLS.lean`](LeanFormalization/Satisfaction/TLS.lean) | C, T, PD, TM, UPT, GUT, CST, CX | TCM, TI, TCI, NCA, EI |
| P-PROT | [`Satisfaction/PPROT.lean`](LeanFormalization/Satisfaction/PPROT.lean) | — | TM, TI, TCM, TCI, NCA |
| Q-PROT | [`Satisfaction/QPROT.lean`](LeanFormalization/Satisfaction/QPROT.lean) | — | TM, TI, TCM, TCI, NCA |

> The Lean code names these axioms `Ax_TSM` and `Ax_TSI` internally; see naming note above.

### Internal Helper Characterizations
The P-PROT and Q-PROT characterizations are proved via intermediate axioms (LTSF and HTSF), which imply NUTC and NDTC respectively:
- P-PROT = C ∧ LTSF ([`Characterizations/PPROT.lean`](LeanFormalization/Characterizations/PPROT.lean))
- Q-PROT = C ∧ HTSF ([`Characterizations/QPROT.lean`](LeanFormalization/Characterizations/QPROT.lean))

### What is not formalized

The following paper results are not included in this formalization:
- Proposition [Equivalences on $\mathbb{R}^n_{\geq 0}$] (collapse from 12 candidate rules to 6)
- Proposition [Axiomatic foundations] (pairwise incompatibility of TCM, TM, NUTC, NDTC)
- Proposition [FOSD classification] (which rules respect FOSD)
- Independence of axioms (Appendix A)
- Incomparability and domain separation results (Appendix C)

### Domain

The paper works on $\mathbb{R}^n_{\geq 0}$ (nonneg reals). The Lean formalization works on all of $\mathbb{R}^n$ (via `Vec n = Fin n → ℝ`), which is strictly more general. The paper notes that the characterizations for PMM, PLS, TMM, and TLS extend to all of $\mathbb{R}^n$.

## Project Structure

```
LeanFormalization/
├── Basic.lean                        Core types (Vec, PrefRel), prefixSum,
│                                     coverageSet, thresholdValues, helper lemmas
├── Examples.lean                     Sanity checks on concrete n=3 vectors
├── Defs/
│   ├── Rules.lean                    Six ranking rules (PMM, PLS, TMM, TLS, P-PROT, Q-PROT)
│   └── Axioms.lean                   All axiom predicates (15 axioms)
├── Characterizations/
│   ├── PMM.lean                      PMM = TCM ∧ TCI
│   ├── TMM.lean                      TMM = TM ∧ TI
│   ├── PLS.lean                      PLS = C ∧ T ∧ PD ∧ NCA
│   ├── TLS.lean                      TLS = C ∧ TM ∧ GUT
│   ├── PPROT.lean                    P-PROT = C ∧ LTSF (internal helper)
│   ├── PPROT_NUTC.lean               P-PROT = C ∧ T ∧ PD ∧ NUTC
│   ├── QPROT.lean                    Q-PROT = C ∧ HTSF (internal helper)
│   └── QPROT_NDTC.lean              Q-PROT = C ∧ T ∧ PD ∧ NDTC
├── Satisfaction/
│   ├── PMM.lean                      PMM axiom satisfaction/violation proofs
│   ├── TMM.lean                      TMM axiom satisfaction/violation proofs
│   ├── PLS.lean                      PLS axiom satisfaction/violation proofs
│   ├── TLS.lean                      TLS axiom satisfaction/violation proofs
│   ├── PPROT.lean                    P-PROT axiom violation proofs
│   └── QPROT.lean                    Q-PROT axiom violation proofs
├── Impossibility/
│   ├── NCA_TM.lean                   NCA vs TM impossibility
│   ├── FOSD_Threshold.lean           FOSD vs NUTC/NDTC (and LTSF/HTSF) impossibility
│   └── NUTC_NDTC.lean                C+T+PD+NUTC+NDTC jointly unsatisfiable
└── Structural/
    └── Refinement.lean               Refinement relations and PCL = PLS
```

## Building

Requires [elan](https://github.com/leanprover/elan) (the Lean version manager).

```bash
lake exe cache get   # download precompiled Mathlib (~5 GB)
lake build           # build all files (~2 min)
```

To verify the formalization is sorry-free:

```bash
grep -r "sorry" LeanFormalization/ --include="*.lean"
# (should produce no output)
```

## Axiom Glossary

| Axiom | Paper | Lean | Intuition |
|-------|-------|------|-----------|
| Completeness | C | `Ax_C` | All pairs are comparable |
| Transitivity | T | `Ax_T` | Consistent rankings |
| Priority Dominance | PD | `Ax_PD` | Dominating in all coordinates implies strict preference |
| Total Monotonicity | TM | `Ax_TM` | Higher total sum implies strict preference |
| Total Independence | TI | `Ax_TI` | Adding the same constant to all coordinates preserves ranking |
| Top-Coordinate Monotonicity | TCM | `Ax_TSM` | Higher top-coordinate value implies strict preference |
| Top-Coordinate Indifference | TCI | `Ax_TSI` | Adding the same constant to the top coordinate preserves ranking |
| Non-Compensatory Advantage | NCA | `Ax_NCA` | A coordinate advantage at a higher-priority state cannot be offset by lower-priority gains |
| Generalized Uniform Transfer | GUT | `Ax_GUT` | A transfer from a lower-priority to a higher-priority state can be compensated by a uniform transfer to all coordinates |
| No Upward Threshold Compensation | NUTC | `Ax_NUTC` | A coverage advantage at a low threshold cannot be compensated by high-threshold differences |
| No Downward Threshold Compensation | NDTC | `Ax_NDTC` | A coverage advantage at a high threshold cannot be compensated by low-threshold differences |
| Uniform Priority Transfer | UPT | `Ax_UPT` | A uniform transfer from coordinate $j+1$ to coordinate $j$ is always beneficial |
| Cross-State Transfer | CST | `Ax_CST` | A transfer from a lower-priority to a higher-priority coordinate is always beneficial |
| Convexity | CX | `Ax_CX` | The preferred set is convex |
| Exchange Invariance | EI | `Ax_EI` | Permuting coordinates yields an indifferent vector |

## Citation

If you use this formalization in your work, please cite:

```bibtex
@article{zambrano2026priority,
  title={Axiomatizations of Priority-Based Ranking Rules},
  author={Zambrano, Eduardo},
  year={2026}
}
```

## License

This formalization is released under the [Apache 2.0 License](LICENSE).
