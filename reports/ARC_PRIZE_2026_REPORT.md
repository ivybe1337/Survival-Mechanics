---
title: "Likely Orders, Allowed Demotes"
subtitle: "A complete report on my ARC Prize 2026 submissions built on Survival Mechanics and FATE"
author: "Joshua Matthew Carter, Independent researcher"
date: "November 2026"
---

## Abstract

I entered both ARC Prize 2026 code tracks with systems built on one idea from my theory: what a model finds likely and what the task allows are different states, and they should be allowed to do different things. A learned score may order candidates. Only evidence that a candidate breaks a law of the task may push it down. On ARC-AGI-2 I added a pre-registered selection layer to the open NVARC pipeline. My linked submission, 57677356, scored 28.06 on the public leaderboard, and a later rerun of identical code, 57913192, scored 29.72. Replayed on the identical candidate pools of the official public-evaluation run, the layer gains one test output of 157 and loses none, while a control that deletes by likelihood loses two. I show exactly why one is the right size: the truth is never generated for 103 of 157 outputs, the generator already respects every local law, and the global laws that catch wrong answers can be declared on only 12 outputs. On ARC-AGI-3 my hidden-set submission, 57913002, scored 0.00. The same code, run on the 25 public games under the official offline scorecard, completed 3 of 183 levels. None of these is a strong score, and I claim none as one. What I claim is an exact accounting of where accuracy goes in a generate-then-select system, a selection rule that held under a deliberate violation, and the evidence for every number, published with this report.

## 1. Introduction

ARC-AGI tests whether a system can learn a new rule from a few examples [1, 2]. The strongest ARC-AGI-2 entries of 2025 generate many candidate answers and then choose two [3, 4]. Choosing is where my theory has something specific to say. In *Likely and Allowed* [6] I separate two states of a history: the predictive state, which fixes what is likely next, and the residual state, which fixes what is still allowed. I prove the two are independent and that a forecaster that uses only one of them can be forced into large errors. An ARC task is a clean place to test that separation, because the demonstrations declare constraints and the model proposes answers.

So I asked a narrow question and fixed my predictions before reading any data: inside a real, competitive solver, what does keeping the two states separate actually buy? This report answers it for ARC-AGI-2, reports honestly on ARC-AGI-3, and explains the code behind every submission.

All numbers below come from files published alongside this report: Kaggle's own submission records pulled with the Kaggle CLI, the notebooks' run logs, the per-output analysis of the official run, and the public leaderboard snapshot. Section 8 lists them.

## 2. The submissions

| Track | Submission | Date | Public score | What it is |
|---|---|---|---|---|
| ARC-AGI-2 | 57913192 | Nov 2, 2026 | 29.72 | Same code, later rerun |
| ARC-AGI-2 | 57677356 | Oct 26, 2026 | **28.06** | Linked submission: V1 admissibility selection over open NVARC; full run analysed |
| ARC-AGI-2 | 56404958 | Sep 20, 2026 | 0.00 | FARSEER exact-program searcher, pipeline validation |
| ARC-AGI-3 | 57913002 | Nov 2, 2026 | **0.00** | DCIE agent through the official gateway |

Source: `kaggle_submissions_arc-agi-2.csv`, `kaggle_submissions_arc-agi-3.csv`. The two ARC-AGI-2 runs of the same code differ by 1.66 points. Section 6 shows why that matters.

## 3. Prior work

The candidate generator is the Qwen3-4B component of NVARC [4], the 2025 winner, as packaged in a public Kaggle notebook whose loader, solver and decoder I use byte for byte. It does per-task LoRA test-time training on augmented demonstrations, depth-first decoding over the ARC tokens, and re-scoring of every candidate under eight augmentations, descending from the ARChitects' approach [5]. I did not write it and I do not claim it.

Constrained decoding enforces rules during generation. I leave generation untouched, so one recorded pool supports every selection rule offline, and the comparison between rules is exact. FATE's elimination step descends from arc consistency [7] and the forward–backward algorithm; what it adds is a logged reason for every removal.

## 4. Approach

### 4.1 The rule

Every system here obeys one rule from the theory: **a learned score may order; only a declared admissibility law may demote or delete.** In the language of the paper, the model's likelihood is a forecast from the predictive state, and an invariant that holds on every demonstration is a piece of the residual state. The rule keeps each state in its own job.

### 4.2 ARC-AGI-2: the selection layer

**Generator (unchanged).** Each test output gets a pool of decoded grids with vote counts and eight augmentation likelihoods. The baseline V0 ranks candidates by votes minus mean negative log-likelihood, exactly as the public pipeline does.

**The ledger, V1 (submitted).** For each task I mine invariants from the demonstrations. An invariant is active only if it holds on every demonstration pair:

- output shape, as a function of input shape;
- palette;
- exact colour counts, conserved from input to output;
- sorted colour profile, the multiset of colour counts conserved from input to output.

Candidates that break an active invariant move behind every admissible candidate. Nothing is deleted, and nothing leaves the two answer slots unless at least two admissible candidates exist.

**FATE, V2 and V3.** FATE intersects forward reachability from the input with backward preimages of the output. It meets in the middle over 60 exact invertible grid operations at depth 2 + 2, plus a global colour map, and it logs the reason for every eliminated state. A program counts only if it reproduces every demonstration. When one exists, its output becomes the first attempt (V2), or the first attempt over the ledger order (V3). On 600 random nondeterministic systems with a planted trajectory, the engine never eliminated a true state.

**Control, V4.** V4 deletes every candidate whose likelihood trails the best by more than ln 10. It breaks the rule on purpose, so the rule can be tested.

**Safety.** Any error in the layer falls back to the pipeline's own order for that task, and a CPU path fills any test output that received no candidate.

**Pre-registration.** I wrote seven predictions before any pool or precision result was read. I report only paired differences between rules on identical pools, because the public checkpoint may have seen public-evaluation tasks during training.

### 4.3 ARC-AGI-3: the agents

ARC-AGI-3 is interactive: an agent plays games it has never seen, through actions, and must discover each game's goal. Every agent below runs the same split. A predictive model learns what the game does, and a survival model records what kills or does nothing.

**DCIE (submitted as 57913002).** Two trainable PyTorch recursive mixture-of-experts models, randomly initialized and trained online on the agent's own observations, with test-time training on every action. It adds survival evidence per state, multi-step counterfactual scoring of actions, and the FARSEER navigation and click policy. In the competition rerun it joins the official `ARC-AGI-3-Agents` framework and plays the games issued by Kaggle's gateway. Its models start with random weights; nothing is pretrained.

**FARSEER v3.** A CPU agent with an online transition model, the FARSEER causal navigation policy, and a click-admissibility ledger. Click outcomes are recorded per game, level and colour under the click as no-op, effect, progress or death. Candidate clicks whose class has only ever been seen as no-op or death move to the back; nothing is deleted.

**FATE 3.** A research agent run after the competition closed: a 26,058,049-parameter model with predictive, survival and policy heads, randomly initialized, with full-weight test-time training on verified transitions and FARSEER navigation to start.

## 5. Results

### 5.1 ARC-AGI-2: the official public-evaluation run

The official commit run covered all 120 public-evaluation tasks: 172 test outputs, 157 of which received at least one candidate. Every task finished; 15 test outputs yielded no grid.

| Rule | Top-2 correct of 157 | Change from V0 |
|---|---|---|
| V0 baseline | 43 | |
| **V1 ledger (submitted)** | **44** | +1, −0 |
| V2 FATE / V3 both | 43 / 44 | +0 / +1 |
| V4 control (deletes by likelihood) | 41 | +0, −2 |
| Top-1 only | 37 | |
| Oracle: truth anywhere in the pool | 54 | |

Task-level bootstrap intervals on the difference from V0 are [0, +3] test outputs for V1 and [−5, 0] for V4; neither is significant (sign test p = 1.0 and 0.5). In task-equivalents the run scores 32.333 under V0 and 33.333 under V1, and my replay reproduces the run's own log exactly. Source: `official_v1_analysis.json`.

**Pre-registered predictions.**

| Prediction | Outcome |
|---|---|
| P1. V1 loses only through false exclusion | Held: no violations |
| P2. The net gain is at most 2 outputs per 100 | Held: 0.64 |
| P3. FATE's certified programs are 40–90% precise | Untestable: 0 of 120 tasks certified |
| P4. FATE adds at most 1 output per 100 | Held: 0 |
| P5. V4 is no better than V1 | Held: 41 against 44 |
| P6. The ledger touches at least 30% of outputs | **Failed: 7.6%** |
| P7. Recall is the binding ceiling | Held |

### 5.2 ARC-AGI-3

| Agent | Run | Games | Levels completed (of 183) | Scorecard | Actions |
|---|---|---|---|---|---|
| DCIE, submitted code | hidden set, 57913002 | hidden | — | **0.00** | — |
| DCIE, same code | public 25, offline | 25 | **3** | 0.186 | 5,192 |
| FATE 3 (after the deadline) | public 25, offline | 25 | 1 | 0.003 | 3,500 |

Neither DCIE nor FATE 3 completed a whole game. The DCIE public run's code is byte-identical to the submitted notebook in all five code cells, so it is the public-set measurement of the submitted agent. By action type, DCIE completed 0 of 93 levels on the 13 keyboard-and-click games, 1 of 29 on the 4 keyboard games, and 2 of 55 on the 7 click games. FATE 3 ran on November 8, after submissions closed, and is research only. Sources: `arc3_public25_dcie.json`, `arc3_public25_fate3.json`, and each run's log.

The FARSEER v3 notebook reports, in its own header, 8 levels and a scorecard of 0.341 at a 500-action budget on the 25 public games against 7 levels and 0.230 for its previous version, with seeds 1 and 2 giving 0.305 against 0.195 and 0.203 against 0.202. The per-game files behind those numbers are not published here, so I do not count them as verified.

**What went wrong on the hidden set.** I submitted the wrong notebook. Submission 57913002 is the DCIE agent through the gateway runner, which is the agent's foundation and scaffolding rather than the agent I meant to enter. The same code completes 3 public levels offline. Levels on the public games do not guarantee levels on the hidden ones, and I do not have the hidden-run logs, so I cannot say whether the agent or the harness failed there.

## 6. Analysis

### 6.1 Where the accuracy goes

Accuracy factors exactly:

$$\frac{44}{172} \;=\; \underbrace{\frac{157}{172}}_{\text{received a pool}} \times \underbrace{\frac{54}{157}}_{\text{truth generated}} \times \underbrace{\frac{44}{54}}_{\text{truth selected}} .$$

Across all 172 test outputs, 157 received a pool. For 103 of those 157 the model never generated the right answer, and no selection rule can recover an answer that is not in the pool. Selection is already efficient: 44 of the 54 available truths reach the top two.

### 6.2 Why a mask has narrow leverage

A demotion rule can win an output only when the truth was generated, sits below the two answer slots, and enough candidates above it break a law. It can lose one only when the truth itself breaks a law and was already in the top two. Eleven outputs had the truth in the pool but outside the top two. Exactly one of them had an inadmissible candidate ahead of the truth, and V1 fixed it. In task `2b83f449`, 13 of the 14 distinct candidates broke the colour profile that every demonstration obeys, and the truth rose from third place to first. That was the layer's entire available gain, and it took it.

The layer is safe. Among the 157 outputs, the ledger excluded the truth once, on `a25697e4_0`, and it cost nothing because the model had never generated the truth there.

### 6.3 Local laws are absorbed; global laws are not

| Invariant | Outputs where it is active | Wrong candidates that violate it |
|---|---|---|
| Output shape | 110 | 0 of 816 |
| Palette | 157 | 1 of 1,155 |
| Exact colour count | 9 | 48 of 74 |
| Sorted colour profile | 3 | 22 of 22 |

Across all pools, 1,084 of 1,155 wrong candidates (93.9%) pass every active invariant. The table shows the mechanism. Wrong candidates essentially never break shape or palette, because a generator fitted to the demonstrations learns what a cell-by-cell decoder can enforce. They break global counting laws often, because no single cell can see a count. My reading is that the binding limit on this residual state is how seldom a global law can be declared, not how well it discriminates: the strong invariants were declarable on only 12 of 157 outputs, and only one of those held a fixable ranking error. This is the split the theory describes between the two states, here measured as a split between laws the predictor already absorbs and laws it cannot.

Finer laws fail differently. Forcing each cell from its 3×3 input neighbourhood is violated by the truth on 74% of applicable outputs and by the wrong top candidate on 68%, so it can neither delete safely nor discriminate.

### 6.4 FATE certified nothing on the evaluation set

FATE certified 0 of 120 evaluation tasks. On the training set it certified 15 of 1,000, of which 14 were correct. My inference is that ARC-AGI-2 evaluation tasks are rarely compositions of global invertible operations, so an exact engine over that library is precise but almost never applicable.

### 6.5 Deleting by likelihood is measurably wrong

Both of V4's losses, `4c3d4a41_1` and `b6f77b65_2`, are correct answers in second place, deleted on likelihood alone. That is the rule's failure mode, observed exactly where the theory says it will appear.

### 6.6 More sampling raises recall, not accuracy

| Fraction of decoded runs | Recall | Top-2 accuracy | Mean candidates |
|---|---|---|---|
| 0.10 | 21.2% | 20.8% | 1.63 |
| 0.25 | 26.2% | 24.5% | 3.01 |
| 0.50 | 30.9% | 26.6% | 4.91 |
| 0.75 | 32.9% | 27.4% | 6.43 |
| 1.00 | 34.4% | 27.4% | 7.70 |

From half the runs to all of them, recall rises 3.5 points and top-2 accuracy only 0.8. The extra truths arrive with few votes, and selection cannot promote them. The run used 5.4 of its 12 hours (`official_v1_task_times.json`).

### 6.7 Noise

My two identical-code runs differ by 1.66 points. The leaderboard agrees with that scale. Among teams scoring 25 to 35 with at most two submissions, the mean is 29.48 with standard deviation 1.40, so 28.06 sits at z = −1.01. Teams in the same band with ten or more submissions average 31.31: the band rises with re-rolls. To detect a one-task effect (0.83 points) at a two-sided 5% level with 80% power takes $n = 2(1.96+0.84)^2\sigma^2/\delta^2$ runs per arm, which is 31 with σ = 1.17 from my pair and 44 with σ = 1.40 from the band. A paired replay on fixed pools costs one run. Leaderboard differences this small are not measurements. Source: `public_leaderboard_2026-11-08.csv`.

## 7. What carries beyond ARC

The accounting is general. Any system that generates candidates and then selects can be split the same way: recall, selection efficiency, and the leverage of each law, all measured on fixed pools before any compute is spent on bigger models. For ARC the numbers point away from selection and toward two things: generator recall, and declaring more global laws, such as relations between colour counts instead of exact conservation, or agreement across a task's test inputs. Those are proposals, not results.

The rule itself carries further. Letting likelihood order and only declared laws demote is the same split a code generator needs between "probably right" and "compiles", and an agent needs between "promising" and "survivable". The theory behind it, with proofs, is *Likely and Allowed* [6].

## 8. Reproducibility and evidence

Everything referenced here is in this repository under `docs/arc/data/`, and the interactive version at `arc.html` recomputes the main numbers in the browser from the same files.

| File | What it holds |
|---|---|
| `kaggle_submissions_arc-agi-2.csv`, `kaggle_submissions_arc-agi-3.csv` | Kaggle's submission records, pulled with the Kaggle CLI |
| `official_v1_analysis.json`, `official_v1_analysis.txt` | Per-output records and summaries of the official ARC-AGI-2 run |
| `invariant_activity.json` | Invariant activity and violations |
| `public_leaderboard_2026-11-08.csv`, `leaderboard_analysis.json` | Public leaderboard snapshot and its analysis |
| `task_2b83f449.json` | The public task the layer fixed |
| `arc3_public25_dcie.json`, `arc3_public25_fate3.json` | Offline scorecards on the 25 public ARC-AGI-3 games |
| `logs/*.log` | Run logs of every notebook named in this report |

The notebooks are on Kaggle under `netphantom17`: `fate-ssm-final` (ARC-AGI-2), `ssm-farseer-arc3-official-gateway-runner` (the ARC-AGI-3 submission), `dcie-ssm-arc3-eval`, `ssm-farseer-v3-arc3` and `fate3-egrwi-public25-rtx6000-research`. The ARC submission code and this report are released under CC BY 4.0, as the ARC Prize rules require; the code is in the public repositories [FATE-ARC-AGI-2](https://github.com/ivybe1337/FATE-ARC-AGI-2) and [DCIE-ARC-AGI-3](https://github.com/ivybe1337/DCIE-ARC-AGI-3). The theory paper is CC BY-SA 4.0 and its proof code MIT-0. The generator, the ARC-AGI-3 framework and the model weights belong to their authors and keep their own licences.

## 9. Conclusion

Keeping what is likely separate from what is allowed was safe in a real solver, and the rule held when I broke it on purpose. It did not measurably raise accuracy, and I can say exactly why: the right answer is usually never generated, the generator already respects every local law, and the global laws that do separate right from wrong can rarely be declared. On ARC-AGI-3 I submitted the wrong notebook and scored 0.00. The same agent completes 3 of 183 public levels. The value of this work is not a score. It is a falsifiable accounting of where accuracy goes, a selection rule with a stated failure mode that showed up exactly where predicted, and every number published with the files that produced it.

## References

[1] F. Chollet, *On the Measure of Intelligence*, arXiv:1911.01547, 2019.
[2] F. Chollet et al., *ARC-AGI-2: A New Challenge for Frontier AI Reasoning Systems*, arXiv:2505.11831, 2025.
[3] F. Chollet et al., *ARC Prize 2025: Technical Report*, arXiv:2601.10904, 2026.
[4] I. Sorokin and J.-F. Puget, *NVARC solution to ARC-AGI-2 2025*, ARC Prize 2025 solution write-up.
[5] D. Franzen, J. Disselhoff and D. Hartmann, *Product of Experts with LLMs: Boosting Performance on ARC Is a Matter of Perspective*, 2025.
[6] J. M. Carter, *Likely and Allowed: The Joint State of Prediction and Admissibility*, 2026, https://doi.org/10.5281/zenodo.24093939.
[7] A. K. Mackworth, *Consistency in Networks of Relations*, Artificial Intelligence 8 (1977), 99–118.
