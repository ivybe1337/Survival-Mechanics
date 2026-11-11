# Safe, Narrow, and Below the Noise Floor

**What an admissibility layer can and cannot do for a test-time-trained ARC-AGI-2 solver**

*ARC Prize 2026 Paper Track submission, as submitted on Kaggle: https://www.kaggle.com/competitions/arc-prize-2026-paper-track/writeups/safe-narrow-and-below-the-noise-floor*

Joshua Matthew Carter, independent researcher. Linked submission `57677356` (public leaderboard 28.06). A later rerun of identical code, `57913192`, scored 29.72.

## Abstract

Strong ARC-AGI-2 entries generate candidate grids, then select two. I add a pre-registered selection layer to the open NVARC pipeline, under one rule from Survival State Mechanics: a learned score may order candidates, and only an invariant mined from the demonstrations may demote them. Replayed on identical official pools, the layer gains one test output of 157 and loses none. The control that deletes by learned score loses two. The truth is missing from 66% of pools. Wrong candidates essentially never break shape or palette invariants (1 of 1,971 checks). Global colour-count invariants catch 65–100% of wrong candidates, but apply to only 12 of 157 outputs. Two identical-code runs differ by two tasks, so no single leaderboard comparison could have seen this effect. My contribution is a falsifiable accounting of where accuracy goes, not a score gain.

## Introduction

ARC-AGI measures few-shot generalisation on novel tasks [1,2]. My inspiration is Survival State Mechanics (SSM), published as *Likely and Allowed* [6], which proves that ε (what is likely next) and κ (what remains admissible) do not determine each other in general. ARC suits this: demonstrations declare constraints and a model proposes answers.

## Prior work

I use the Qwen3-4B component of NVARC [3,4], the 2025 winner, packaged in the public notebook `mikelou1/arc-agi2-lb33-89-minimal-perfpatch`, whose loader, solver and decoder cells mine match byte for byte, descending from the ARChitects' approach [5]. Unlike constrained decoding, I leave generation untouched, so one recorded pool supports every selection rule. FATE's elimination step descends from arc consistency [7].

## Approach

**Model and generator (unchanged).** The only learned model is the Qwen3-4B checkpoint `sorokin/qwen3_4b_grids15_sft139`, on four L4 GPUs. For each task a fresh LoRA adapter (rank 256) trains for one epoch (AdamW, lr 5×10⁻⁵, cosine) on 16 augmented copies. Each test output is decoded from up to 16 symmetry-and-colour views. DFS keeps only complete grids above 20% probability (cumulative NLL < −ln 0.2), so at most four per view; 1,391 of 1,867 non-empty views returned exactly one. Each new grid is re-scored on eight augmentations. Baseline V0 ranks by votes minus mean negative log-likelihood.

**κ-ledger (V1, submitted).** An invariant is active only if it holds on every demonstration: output shape (same or transposed), palette (test-input colours plus any colour an output introduces), exact colour counts, or sorted colour profile. Candidates failing an active invariant move behind all admissible ones and fill a slot only if fewer than two remain. Nothing is deleted.

**FATE (V2, V3; inactive in submitted V1).** Intended to override ranking when a task is provably an exact program. From the first demonstration it enumerates forward images of the input and exact preimages of the output over 60 invertible grid operations (depth 2+2), joins them on grid equality, and eliminates programs failing any other demonstration; failing that, it fits one global colour map. A surviving program's output is forced to the front.

**Control (V4).** Deletes candidates whose likelihood trails the best by more than ln 10. A deliberate violation.

Predictions were written before any pool was read. I report paired differences only, since the checkpoint may have seen public-evaluation tasks. Hidden-set pools are unobservable, so every replay uses public evaluation. Public-evaluation V1 reached 27.8% of tasks against 28.06 hidden: no sign of exposure advantage, though the sets differ.

## Results

**Public leaderboard (Figure 1).** The linked submission scored 28.06, which is 33⅔ of 120 tasks; Kaggle lists the team there, rank 2,158 of 3,544. The identical-code rerun scored 29.72 (35⅔). The field's top score is 88.06, so this entry is not competitive on accuracy. The notebooks differ only in a markdown header and the commit-mode task list, so both hidden-set runs executed identical code.

**Official public-evaluation run** (v1 commit, all 120 tasks; 172 outputs; 15 yielded no grid although every task finished, leaving 157 pools):

| Rule | Top-2 correct | vs V0 |
|---|---|---|
| V0 baseline | 43 | |
| V1 ledger (submitted) | 44 | +1, −0 |
| V2 FATE / V3 both | 43 / 44 | +0 / +1 |
| V4 control | 41 | +0, −2 |
| Oracle over pool | 54 | |

Task-level bootstrap intervals are [0, +3] test outputs for V1 and [−5, 0] for V4. Neither is significant (sign test p = 1.0 and 0.5). Task-equivalents: 32.333 versus 33.333. Both V4 losses were correct second-place answers.

**Pre-registration.** Held: P1 V1 loses only through false exclusion (0 violations); P2 gain ≤ 2 per 100 (0.64); P4 FATE adds ≤ 1 per 100 (0); P5 V4 no better than V1 (41 vs 44); P7 recall is the binding ceiling. Untestable: P3 FATE precision (0 of 120 certified). **Failed: P6, ledger touches ≥ 30% of outputs (7.6%).**

**Run log (public evaluation).** All 120 tasks trained (128 steps each; median loss 0.008, 165 s) and finished, using 20.8 GPU-hours, 6.7 of them training, and 5.4 of 12 wall-clock hours. Six hit the 1,200-second task limit. The mask changed the top two on 5 outputs and correctness on one. The log's own variant table prints every count above.

## Why the effect is small

Accuracy factors exactly (Figure 2): 44/172 = (157/172 received a pool) × (54/157 truth generated) × (44/54 selected).

**A mask has narrow leverage.** It can win only if the truth was generated, ranked below slot 2, and enough candidates above it are inadmissible. It can lose only if the truth is inadmissible and was already in the top two. Eleven outputs were generated but missed; exactly one had an inadmissible candidate ahead. V1 fixed it. In `2b83f449_0`, 13 of 14 candidates broke the demonstrations' colour profile and the truth moved from third place to first.

**The layer was safe here.** The ledger excludes the truth on 2 of 172 outputs, at no cost: the truth was not generated there.

**Local invariants are absorbed; global ones are not.** Overall, 93.9% of wrong candidates are admissible:

| Invariant | Outputs active | Wrong candidates violating |
|---|---|---|
| Shape | 110 | 0 of 816 |
| Palette | 157 | 1 of 1,155 |
| Exact colour count | 9 | 48 of 74 |
| Sorted colour profile | 3 | 22 of 22 |

My hypothesis: a generator fitted to the demonstrations learns what a cell-by-cell decoder can enforce, and does not learn global counting, which no single cell can see. The independence theorem of [6] concerns exact objects, and this run does not test it. The strongest invariants are the rarest: they were declarable on 12 of 157 outputs, and only one of those held a fixable ranking error. Small and clustered: 13 of the 22 profile violations come from one output. **The binding limit on this κ is how seldom a global invariant can be declared, not how well it discriminates.**

**FATE certified nothing.** Zero of 120 tasks. My inference: ARC-AGI-2 tasks are rarely compositions of global invertible operations.

**Generation is the main loss, and late sampling bought little accuracy (Figure 3).** For 103 of 157 outputs the truth was never generated. From half the decoded runs to all of them, recall rises 3.5 points but top-2 only 0.8. Missed truths hold a median of 2 votes (10.5% of samples) and selected truths 8 (37.5%), consistent with late arrivals staying below slot 2. A truth enters the pool only if some view gives the whole grid over 20%; lowering that threshold is untested.

## Noise

My two runs differ by 1.66 points. Among teams scoring 25–35, those with at most two submissions average 29.48 (SD 1.40), so my 28.06 is z = −1.01. Teams with ten or more average 31.31, consistent with re-rolling. Detecting a one-task effect at 80% power needs 31–44 full runs per arm (SD 1.17 from one pair, which is crude; 1.40 from the band). Paired replay on fixed pools costs one run.

## Conclusion

The layer lost nothing and the deliberate violation lost two answers, but neither difference is significant, and the layer did not measurably raise accuracy. The accounting generalises to any generate-then-select system: measure recall, selection efficiency and mask leverage on fixed pools before spending compute. For ARC, I would redirect effort to generator recall, starting with the decoder threshold, and to declaring more global invariants, such as colour-count relations rather than exact conservation. These are untested proposals.

**Code:** https://www.kaggle.com/code/netphantom17/fate-ssm-final. **Run details, receipts and my other FATE submissions:** https://ivybe1337.github.io/Survival-Mechanics/arc.html. **Theory and Lean proofs:** https://github.com/ivybe1337/Survival-Mechanics. **License:** CC BY 4.0 (writeup, FATE/SSM code), per track rules.

## References

[1] Chollet, *On the Measure of Intelligence*, arXiv:1911.01547. [2] Chollet et al., *ARC-AGI-2*, arXiv:2505.11831. [3] Chollet et al., *ARC Prize 2025: Technical Report*, arXiv:2601.10904. [4] Sorokin & Puget, *NVARC solution to ARC-AGI-2 2025*. [5] Franzen, Disselhoff & Hartmann, *Product of Experts with LLMs*. [6] Carter, *Likely and Allowed: The Joint State of Prediction and Admissibility*, v1.0, 2026, https://doi.org/10.5281/zenodo.24093939. [7] Mackworth, *Consistency in Networks of Relations*, 1977.
