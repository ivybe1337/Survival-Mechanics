# Likely and Allowed: Lean 4 formalization

Machine-checked proofs for *Likely and Allowed: The Joint State of Prediction and Admissibility* (Joshua Matthew Carter, v1.0, November 2026).

The names follow the paper: `V : List α → Bool` is an admissibility rule, `resSet V h` is the residual set `R_V(h)`, the classes of `ResEquiv V` are the residual states `κ`, `AdmMonotone V` says death is absorbing, and `Process.survProb` is the survival probability `S_n`.

`LEAN_MAP.md` lists, for each result in the paper, the Lean file and theorem names, and notes where a Lean statement is a slight variant of the printed one.

## Files

All sources are under `LikelyAllowed/`; `LikelyAllowed.lean` imports every file.

| File | Contents |
|---|---|
| `Residual.lean` | semantics, residual equivalence, admissibility rules and residual sets, the dead class, finite tests |
| `Moore.lean` | finite tests suffice (Moore's bound) |
| `Canonical.lean` | deterministic presentations and the canonical machine |
| `Joint.lean` | right congruences, joint equivalence, index bounds |
| `Predictive.lean` | processes, predictive state, joint state, three canonical machines |
| `ShortFutures.lean` | short continuations suffice for finite-dimensional processes |
| `Independence.lean` | prediction and admissibility are independent |
| `Conditioned.lean` | survival probability, conditioned forecasts, sufficiency of the joint state |
| `Exactness.lean` | survival-aware prediction is exactly the joint state; positivity is needed |
| `Decisions.lean` | decisions factor through the joint state |
| `Lookahead.lean` | lookahead feasibility is 1-Lipschitz |
| `Planning.lean` | planning with approximate residual states |
| `Certificates.lean` | minimal non-members, Sperner and rank bounds |
| `Nondet.lean` | universal (nondeterministic) presentations, fooling sets |
| `Succinct.lean` | exponential succinctness |
| `Support.lean` | what the forecasts see without full support: supported residual and joint state, Corollary 5.6 |
| `Audit.lean` | `#print axioms` for every main theorem |

## Checking

Requires `elan`. From this directory:

```
lake exe cache get     # download prebuilt Mathlib
lake build             # checks every proof
lake env lean LikelyAllowed/Audit.lean   # prints the axioms used by each main theorem
```

Built with `lake build`: 1,964 jobs, no errors, no warnings. `Audit.lean` prints the axioms of 159 theorems. The development contains no `sorry`, no `native_decide`, and no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.

Toolchain: `leanprover/lean4:v4.35.0-rc3`, Mathlib `v4.35.0-rc3`.
