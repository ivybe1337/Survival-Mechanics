# Survival Mechanics

## Likely and Allowed: The Joint State of Prediction and Admissibility

Joshua Matthew Carter

**[Read the paper online](https://ivybe1337.github.io/Survival-Mechanics/)** · **[PDF](paper/Likely_and_Allowed.pdf)**

Give a forecaster the exact probability law of a process, then ask what happens next given that the future must obey a declared rule. If it ignores which futures the rule still allows, it can be forced to be wrong by nearly as much as any forecaster can be: error approaching $1-1/d$ on a $d$-symbol alphabet. A model can predict the next word perfectly and still write code that will not compile. Knowing what is likely is not knowing what is allowed, and I make that distinction exact. A history carries two states: its predictive state $\varepsilon$, which fixes its future law, and its residual state $\kappa$, which fixes which continuations a separately declared rule still admits. Each is classical on its own. I prove that the pair $J=(\varepsilon,\kappa)$ is exactly the state of survival-aware prediction. Every survival probability and every survival-conditioned forecast depends only on $J$. Conversely, under full support those forecasts recover $J$ after the finite horizon $\max(k-2,\,m-1)$, and no shorter horizon works in general. The converse survives noise. Forecasts that agree within an explicit margin pin down the residual state exactly and the predictive state to within a bound set by an observability constant, and I give counterexamples showing that neither constant can be dropped. The same state gives value bounds for planning, tight bounds on certificate bases for search by elimination, and a sharp map of when the canonical machine is canonical. The core theorems are machine-checked in Lean 4 (159 theorems, standard axioms only), and every finite claim is reproduced in exact arithmetic.

## Contents

- `paper/`: the paper as PDF and Markdown with LaTeX, and its figure.
- `lean/`: the Lean 4 + Mathlib formalization, library `LikelyAllowed`. `LEAN_MAP.md` maps every formalized result to its Lean names.
- `receipts/`: exact-arithmetic reproduction scripts. Integer and rational arithmetic only.
- `docs/`: the web version of the paper.

## Checking it

The proofs:

```
cd lean
lake exe cache get
lake build
lake env lean LikelyAllowed/Audit.lean
```

The build is 1,964 jobs with no errors or warnings, and the audit prints the axioms of 159 theorems: only `propext`, `Classical.choice` and `Quot.sound` appear.

The finite computations:

```
cd receipts
python3 run_release.py
python3 r8_extensions.py
```

`run_release.py` writes `MANIFEST.json` with the SHA-256 digest of every receipt. A rerun that reproduces a digest reproduces every number in it.

## Linked code submission

My ARC Prize 2026 entry for the ARC-AGI-2 track is the Kaggle notebook `netphantom17/fate-ssm-final` (submission 57913192). The paper says what it does and does not show, and gives a legend from the notebook's terms to the paper's.

## Citation

```
@misc{carter2026likely,
  author       = {Joshua Matthew Carter},
  title        = {Likely and Allowed: The Joint State of Prediction and Admissibility},
  year         = {2026},
  howpublished = {\url{https://ivybe1337.github.io/Survival-Mechanics/}}
}
```

## License

The paper text and figures are licensed under the [Creative Commons Attribution-ShareAlike 4.0 International License](https://creativecommons.org/licenses/by-sa/4.0/) (CC BY-SA 4.0). The code in `lean/` and `receipts/` is licensed under MIT-0 (MIT No Attribution); see `LICENSE`.
