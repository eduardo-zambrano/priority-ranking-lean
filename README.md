# Lean 4 Formalization: Axiomatizations of Priority-Based Ranking Rules

Formal verification companion to "Axiomatizations of Priority-Based Ranking Rules" by Eduardo Zambrano. Built with Lean 4 (v4.28.0) and Mathlib.

## Status

All six characterization theorems compile sorry-free.

| # | Characterization | File | Status |
|---|---|---|---|
| 1 | PMM = TSM + TSI | `Characterizations/PMM.lean` | sorry-free |
| 2 | TMM = TM + TI | `Characterizations/TMM.lean` | sorry-free |
| 3 | PLS = C + T + PD + NCA | `Characterizations/PLS.lean` | sorry-free |
| 4 | TLS = C + TM + GUT | `Characterizations/TLS.lean` | sorry-free |
| 5 | P-PROT = C + T + PD + NUTC | `Characterizations/PPROT_NUTC.lean` | sorry-free |
| 6 | Q-PROT = C + T + PD + NDTC | `Characterizations/QPROT_NDTC.lean` | sorry-free |

Additional sorry-free results:
- P-PROT = C + LTSF (`Characterizations/PPROT.lean`) — internal helper characterization
- Q-PROT = C + HTSF (`Characterizations/QPROT.lean`) — internal helper characterization
- NCA vs TM impossibility (`Impossibility/NCA_TM.lean`)
- Refinement relations (`Structural/Refinement.lean`)
- PCL = PLS equivalence (`Structural/Collapse.lean`)
- PMM and TMM axiom satisfaction (`Satisfaction/PMM.lean`, `Satisfaction/TMM.lean`)

## Project Structure

```
LeanFormalization/
  Basic.lean                  -- Core types, prefixSum, coverageSet, helper lemmas
  Defs/
    Rules.lean                -- PMM, PLS, TMM, TLS, P-PROT, Q-PROT definitions
    Axioms.lean               -- All axiom predicates (C, T, PD, NCA, TM, etc.)
    FOSD.lean                 -- FOSD definition
  Characterizations/          -- Iff theorems for each rule
  Satisfaction/               -- Which axioms each rule satisfies
  Impossibility/              -- Impossibility theorems
  Structural/                 -- Refinement, collapse, FOSD classification
```

## Building

```bash
lake exe cache get   # download precompiled Mathlib
lake build           # build all files
```

## Remaining sorrys (lower priority)

- 10 in `Satisfaction/PPROT.lean` and `Satisfaction/QPROT.lean` (counterexample computations)
- 2 in `Impossibility/FOSD_Threshold.lean` (counterexample computations)
