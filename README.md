# Lean 4 Formalization: Axiomatizations of Priority-Based Ranking Rules

Formal verification companion to **"Axiomatizations of Priority-Based Ranking Rules"** by Eduardo Zambrano. Built with [Lean 4](https://lean-lang.org/) v4.28.0 and [Mathlib](https://leanprover-community.github.io/) (pinned in `lake-manifest.json`).

## Overview

The paper axiomatizes six ranking rules for comparing vectors in $\mathbb{R}^n$ when coordinates have an exogenous priority order (e.g., journal quality tiers, risk categories). This repository contains a complete, sorry-free formalization of all six characterization theorems, three impossibility results, structural relationships, and axiom satisfaction/violation proofs.

## Characterization Theorems

Each characterization theorem is an `iff`: the rule equals the conjunction of its axioms.

| Rule | Characterization | Axioms | File |
|------|------------------|--------|------|
| PMM | PMM = TCM ∧ TCI | Top-Coordinate Monotonicity, Top-Coordinate Indifference | [`Characterizations/PMM.lean`](LeanFormalization/Characterizations/PMM.lean) |
| PLS | PLS = C ∧ T ∧ PD ∧ NCA | Completeness, Transitivity, Pareto Dominance, Non-Compensability Across Levels | [`Characterizations/PLS.lean`](LeanFormalization/Characterizations/PLS.lean) |
| TMM | TMM = TM ∧ TI | Total Monotonicity, Total Indifference | [`Characterizations/TMM.lean`](LeanFormalization/Characterizations/TMM.lean) |
| TLS | TLS = C ∧ TM ∧ GUT | Completeness, Total Monotonicity, Generalized Upward Transfer | [`Characterizations/TLS.lean`](LeanFormalization/Characterizations/TLS.lean) |
| P-PROT | P-PROT = C ∧ T ∧ PD ∧ NUTC | Completeness, Transitivity, Pareto Dominance, No Upward Threshold Compensation | [`Characterizations/PPROT_NUTC.lean`](LeanFormalization/Characterizations/PPROT_NUTC.lean) |
| Q-PROT | Q-PROT = C ∧ T ∧ PD ∧ NDTC | Completeness, Transitivity, Pareto Dominance, No Downward Threshold Compensation | [`Characterizations/QPROT_NDTC.lean`](LeanFormalization/Characterizations/QPROT_NDTC.lean) |

The characterization theorems are formalized for arbitrary $n$.

> **Naming note.** The Lean code uses `Ax_TSM` / `Ax_TSI` (Top-State Monotonicity / Indifference) where the paper uses TCM / TCI (Top-Coordinate Monotonicity / Indifference). These are identical definitions; the paper's naming was finalized after the formalization was written.

## Impossibility Theorems

| Theorem | Statement | File |
|---------|-----------|------|
| NCA and TM are incompatible | NCA ∧ TM → ⊥ | [`Impossibility/NCA_TM.lean`](LeanFormalization/Impossibility/NCA_TM.lean) |
| FOSD-respect and threshold non-compensation are incompatible | FOSD ∧ NUTC → ⊥ and FOSD ∧ NDTC → ⊥ | [`Impossibility/FOSD_Threshold.lean`](LeanFormalization/Impossibility/FOSD_Threshold.lean) |
| NUTC and NDTC cannot be reconciled | C ∧ T ∧ PD ∧ NUTC ∧ NDTC → ⊥ | [`Impossibility/NUTC_NDTC.lean`](LeanFormalization/Impossibility/NUTC_NDTC.lean) |

All three are formalized at $n = 2$, the minimal case; the paper extends them to general $n$ by an elementary zero-padding argument. `FOSD_Threshold.lean` also proves the stronger intermediate result that FOSD-respect is incompatible with LTSF and HTSF (the biconditional threshold-scanning axioms).

## Structural Results

- **PLS refines PMM** and **TLS refines TMM** ([`Structural/Refinement.lean`](LeanFormalization/Structural/Refinement.lean))
- **PCL = PLS**: the prefix-sum lexicographic rule equals PLS on all of $\mathbb{R}^n$ ([`Structural/Refinement.lean`](LeanFormalization/Structural/Refinement.lean))

## Axiom Satisfaction and Violation

These files, together with the `satisfies` lemmas inside the characterization files (which prove each rule's defining axioms), verify every satisfaction (✓) entry and every within-family violation (✗) entry of the paper's axiom tables (Section 4 and Appendix B).

| Rule | Satisfies | Violates | File |
|------|-----------|----------|------|
| PMM | C, T, TCM, TCI, NCA, CST, CX | PD, TM, TI, GUT, NUTC, NDTC | [`Satisfaction/PMM.lean`](LeanFormalization/Satisfaction/PMM.lean) |
| PLS | C, T, PD, NCA, TCM, UPT, CST, CX | TM, TI, TCI, GUT, EI, NUTC, NDTC | [`Satisfaction/PLS.lean`](LeanFormalization/Satisfaction/PLS.lean) |
| TMM | C, T, TM, TI, PD, CST, CX, EI | TCM, TCI, NCA, GUT, NUTC, NDTC | [`Satisfaction/TMM.lean`](LeanFormalization/Satisfaction/TMM.lean) |
| TLS | C, T, PD, TM, GUT, UPT, CST, CX | TCM, TI, TCI, NCA, EI, NUTC, NDTC | [`Satisfaction/TLS.lean`](LeanFormalization/Satisfaction/TLS.lean) |
| P-PROT | C, T, PD, NUTC | TM, TI, TCM, TCI, NCA, GUT, NDTC | [`Satisfaction/PPROT.lean`](LeanFormalization/Satisfaction/PPROT.lean) |
| Q-PROT | C, T, PD, NDTC | TM, TI, TCM, TCI, NCA, GUT, NUTC | [`Satisfaction/QPROT.lean`](LeanFormalization/Satisfaction/QPROT.lean) |

This covers **every** entry (all ✓ and all ✗) of the paper's Section 4 axiom table. Satisfaction lemmas are proved for arbitrary $n$; violation lemmas exhibit explicit counterexamples at $n = 2$ (or $n = 3$ where the $n = 2$ case degenerates, e.g. PMM vs. GUT). The cross-family violations route through [`Satisfaction/Witnesses.lean`](LeanFormalization/Satisfaction/Witnesses.lean), which exploits the fact that the NUTC (resp. NDTC) hypotheses for a pair are precisely `PPROT_strict` (resp. `QPROT_strict`).

## Internal Helper Characterizations

The P-PROT and Q-PROT characterizations are proved via intermediate axioms (LTSF and HTSF), which imply NUTC and NDTC respectively:

- P-PROT = C ∧ LTSF ([`Characterizations/PPROT.lean`](LeanFormalization/Characterizations/PPROT.lean))
- Q-PROT = C ∧ HTSF ([`Characterizations/QPROT.lean`](LeanFormalization/Characterizations/QPROT.lean))

## What is not formalized

- Proposition [Equivalences on $\mathbb{R}^n_{\geq 0}$] (collapse from 12 candidate rules to 6)
- Proposition [Axiomatic foundations] (pairwise incompatibility of TCM, TM, NUTC, NDTC)
- Proposition [FOSD classification] (which rules respect FOSD)
- Independence of axioms (Appendix A)
- Incomparability and domain separation results (Appendix C)

## Domain

The paper works on $\mathbb{R}^n_{\geq 0}$; the formalization defines everything on all of $\mathbb{R}^n$ (`Vec n = Fin n → ℝ`) with no nonnegativity hypothesis, which is strictly more general. This matches the paper's domain analysis (Appendix C): all six characterization theorems hold on all of $\mathbb{R}^n$; only the collapse-to-six proposition requires nonnegativity.

## Project Structure

```
LeanFormalization/
├── Basic.lean                Core types (Vec, PrefRel), prefixSum, coverageSet,
│                             thresholdValues, helper lemmas
├── Examples.lean             Sanity checks on concrete n=3 vectors
├── Defs/
│   ├── Rules.lean            Six ranking rules (PMM, PLS, TMM, TLS, P-PROT, Q-PROT)
│   └── Axioms.lean           All axiom predicates
├── Characterizations/
│   ├── PMM.lean              PMM = TCM ∧ TCI
│   ├── TMM.lean              TMM = TM ∧ TI
│   ├── PLS.lean              PLS = C ∧ T ∧ PD ∧ NCA
│   ├── TLS.lean              TLS = C ∧ TM ∧ GUT
│   ├── PPROT.lean            P-PROT = C ∧ LTSF (internal helper)
│   ├── PPROT_NUTC.lean       P-PROT = C ∧ T ∧ PD ∧ NUTC
│   ├── QPROT.lean            Q-PROT = C ∧ HTSF (internal helper)
│   └── QPROT_NDTC.lean       Q-PROT = C ∧ T ∧ PD ∧ NDTC
├── Satisfaction/
│   ├── Witnesses.lean        NUTC/NDTC bridge lemmas + concrete witnesses
│   ├── PMM.lean              PMM axiom satisfaction/violation proofs
│   ├── TMM.lean              TMM axiom satisfaction/violation proofs
│   ├── PLS.lean              PLS axiom satisfaction/violation proofs
│   ├── TLS.lean              TLS axiom satisfaction/violation proofs
│   ├── PPROT.lean            P-PROT axiom satisfaction/violation proofs
│   └── QPROT.lean            Q-PROT axiom satisfaction/violation proofs
├── Impossibility/
│   ├── NCA_TM.lean           NCA vs TM impossibility
│   ├── FOSD_Threshold.lean   FOSD vs NUTC/NDTC (and LTSF/HTSF) impossibility
│   └── NUTC_NDTC.lean        C+T+PD+NUTC+NDTC jointly unsatisfiable
└── Structural/
    └── Refinement.lean       Refinement relations and PCL = PLS
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
| Pareto Dominance | PD | `Ax_PD` | Weakly better in every coordinate and strictly better in some implies strict preference |
| Total Monotonicity | TM | `Ax_TM` | Higher total sum implies strict preference |
| Total Indifference | TI | `Ax_TI` | Equal totals imply indifference |
| Top-Coordinate Monotonicity | TCM | `Ax_TSM` | Higher top coordinate implies strict preference |
| Top-Coordinate Indifference | TCI | `Ax_TSI` | Equal top coordinates imply indifference |
| Non-Compensability Across Levels | NCA | `Ax_NCA` | No amount of lower-tier performance can compensate for a higher-tier deficit |
| Generalized Upward Transfer | GUT | `Ax_GUT` | Moving mass to any combination of higher-priority coordinates, total preserved, is strictly better |
| No Upward Threshold Compensation | NUTC | `Ax_NUTC` | A coverage advantage at a low threshold cannot be compensated by high-threshold differences |
| No Downward Threshold Compensation | NDTC | `Ax_NDTC` | A coverage advantage at a high threshold cannot be compensated by low-threshold differences |
| Upward Priority Transfer | UPT | `Ax_UPT` | Transferring mass from coordinate $k+1$ to coordinate $k$, total preserved, is strictly better |
| Coordinate Sure-Thing | CST | `Ax_CST` | Coordinates where the two vectors agree do not affect the ranking |
| Convexity | CX | `Ax_CX` | Weak upper contour sets are convex |
| Exchange Invariance | EI | `Ax_EI` | Permuting coordinates yields an indifferent vector |
| Respect for FOSD | — | `Ax_FOSD_mono` | Strict FOSD dominance (in the priority setting) implies strict preference |

## Citation

If you use this formalization in your work, please cite:

```bibtex
@unpublished{zambrano2026priority,
  title={Axiomatizations of Priority-Based Ranking Rules},
  author={Zambrano, Eduardo},
  year={2026},
  note={Working paper, California Polytechnic State University}
}
```

## License

This formalization is released under the [Apache 2.0 License](LICENSE).
