# Likely and Allowed ↔ Lean map

This table maps each numbered result of *Likely and Allowed: The Joint State of Prediction and
Admissibility* (v1.0) to its Lean 4 + Mathlib formalization. Lean names are relative to the
namespace `LikelyAllowed`, and files are under `LikelyAllowed/`. Every name listed here exists and
builds. `lake build` checks the whole development, and `lake env lean LikelyAllowed/Audit.lean`
prints the axioms of every main theorem. Only `propext`, `Classical.choice` and `Quot.sound` appear.

Vocabulary: `V : List α → Bool` is an admissibility rule; `resSet V h` is the residual set
`R_V(h)`; the classes of `ResEquiv V` are the residual states `κ`; `AdmMonotone V` says death is
absorbing; `Process.survProb` and `Process.condLaw` are the survival probability `S_n` and the
survival-conditioned forecast `Q_n` of Section 5. Section 2.5 (excluded continuations) and
Section 9 (connection to Recursive Asymmetric Duality) are proved in the text and checked by
`verify_exclusion_interface.py`; they are not formalized here.

Alphabet `Σ` is an arbitrary type `α` and words are `List α`. Where a concrete alphabet is used,
`a = false` and `b = true`.

| Result | File | Lean name(s) | Exact / variant |
|---|---|---|---|
| Def 2.1 | Residual | `residual`, `ResEquiv`, `resSetoid` | exact (any codomain `X`) |
| Lemma 2.2 | Residual | `resEquiv_equivalence`, `resEquiv_snoc`, `resEquiv_append_right` | exact |
| Lemma 2.3 | Residual | `residual_factors_iff`, `residual_factors_through_class`, `class_factors_through` | exact (both directions, plus "coarsest") |
| Def 2.4 | Residual | `resSet`, `AdmMonotone`, `resEquiv_iff_resSet_eq` | exact |
| Lemma 2.5 | Residual | `resEquiv_dead_iff`, `resEquiv_of_resSet_empty`, `resSet_append_empty`, `resSet_empty_iff` | exact |
| Prop 2.6 | Residual | `totalize`, `resSet_totalize_of_mem`, `resSet_totalize_of_not_mem`, `admMonotone_totalize` | variant: `V_H` is a total function whose values off `H` are ignored |
| Prop 2.7 | Residual, Moore | (a) `testEquiv_anti`, `testEquiv_univ_iff`; (b) `resEquiv_iff_lenTest`, `resEquiv_of_index_one` | exact; (b) is proved for every codomain, with `ind` as `Nat.card` of a `Finite` quotient |
| Example 2.8 | Nondet | `noBB`, `noBB_iff`, `Dκ_reach_eq_iff`, `noBB_index` | exact (three classes `A, B, D`) |
| Def 2.9 | Predictive, ShortFutures | `Process`, `Process.p_append_le`, `Process.p_le_one`, `LinRep` | variant: `p` is `ℝ`-valued and nonnegative; `p ≤ 1` is derived |
| Def 2.10 | Predictive | `Process.pred`, `Process.EpsEquiv`, `Process.epsSetoid` | exact |
| Lemma 2.11 | Predictive | `Process.epsEquiv_equivalence`, `Process.epsEquiv_rightCongr`, `Process.pred_eq_of_epsEquiv`, `Process.epsEquiv_iff_resEquiv_Phi` | exact |
| Lemma 2.12 | ShortFutures | `LinRep.epsEquiv_iff_short`; Krylov core: `dotProduct_eq_zero_of_short`, `mem_krylov_dim_sub_one` | exact (dimension `m`, horizon `m - 1`) |
| Def 2.13 | Predictive, Joint | `Process.JEquiv`, `Process.jEquiv_iff_resEquiv_pair`, `Process.jEquiv_rightCongr`, `Process.jSetoid_eq_inf`, `RightCongr.inf` | exact |
| Def 3.1 | Canonical | `DetPres`, `DetPres.IsExact`, `DetPres.IsReachable`, `DetPres.Hom`, `canonical` | exact |
| Thm 3.2 | Canonical | (a) `canonical_isExact`, `canonical_isReachable`; (b) `existsUnique_hom_canonical`, `DetPres.Hom.surjective_toCanonical`; (c) `DetPres.Hom.bijective_iff_kernel`, `DetPres.Hom.inv`, `iso_canonical_of_bijective`; (d) `DetPres.Hom.bijective_iff_card`, `card_canonical_le` | exact for any codomain; (d) uses `[Finite S]` and `Nat.card` |
| Cor 3.3 | Predictive | `Process.three_machines`, `Process.index_J_eq_reachable_pairs` | exact |
| Thm 4.1 | Independence | (a) `parity_epsEquiv_iff`, `parity_index_eps`; (b) `noBB_index`; (c) `parity_index_J`, `sixReps_pairwise_not_jEquiv`; (d) `parity_incomparable` | exact (`α, β` are named `pa, pb`) |
| Prop 4.2 | Joint, Predictive | `card_quotient_inf_le_mul`, `max_card_quotient_le_card_inf`, `card_inf_eq_right_iff`, `card_inf_eq_left_iff`, `incomparable_iff_max_lt`; for J: `Process.index_sandwich`, `Process.index_eq_iff` | variant: assumes `ind ε, ind κ < ∞` rather than `ind J < ∞` (the two are equivalent by the sandwich); general form holds for any two setoids |
| Cor 4.3 | Joint | `refines_inf_of_classes_factor`, `refines_joint_of_classes_factor`, `refines_joint_of_residuals_factor` | exact |
| Def 5.1 | Conditioned | `words`, `Process.survProb`, `Process.condLaw`, `Process.survInf`, `Process.condLawInf` | variant: `S_∞` is any functional of the sequence `(S_n)` (limit, infimum, …); Lean's `x/0 = 0` fills undefined `Q_n` |
| Lemma 5.2 | — | not formalized | measure-theoretic (continuity from above) |
| Prop 5.3 | Conditioned | `Process.sum_pred_mul_eq_of_jEquiv`, `Process.sum_pred_mul_resSet_eq_of_jEquiv`, `Process.survProb_eq_of_jEquiv`, `Process.condLaw_eq_of_jEquiv`, `Process.survInf_eq_of_jEquiv`, `Process.condLawInf_eq_of_jEquiv` | exact for `n ∈ ℕ ∪ {∞}`; no monotonicity needed; the limit-of-marginals clause (Q-process) is not stated separately |
| Thm 5.4 | Exactness | (a) `Process.forecasts_eq_iff_jEquiv`, `Process.jEquiv_of_forecasts_eq`, `Process.survives_iff`; (b) `Process.truncated_forecasts_eq_iff_jEquiv`, `Process.resEquiv_of_truncated_forecasts_eq`; (c) `positivity_necessary`, `Vab_not_resEquiv`, `allA_not_allPos` | exact: in (b) any `H ≥ max(k-2, m-1)` works; `Q_n` is compared on `Σ^n`; monotonicity is not needed |
| Rem 5.5, Prop 5.7, Examples 5.8 and 5.9 | — | not formalized | concrete real-number computations |
| Cor 5.6 | Support | `Process.forecasts_eq_iff_jpEquiv`, `Process.jpEquiv_of_forecasts_eq`, `Process.blind_agree`, `resP`, `JpEquiv` | exact for `h, h' ∈ Supp p`, no positivity hypothesis; finite instances also in receipt R7 |
| Prop 6.1 | Decisions | (a) `feasible_eq_of_resEquiv`; (b) `argmax_eq_of_stat`, `Process.argmax_eq_of_jEquiv`; (c) `policyValue_eq_of_stat`, `Process.policyValue_eq_of_jEquiv` | variant: stated for any right-congruent statistic refining `κ`, then instantiated at `J`; (c) needs no feasibility hypothesis on `π`; `⊥` is `none` |
| Prop 6.2 | Lookahead | `card_lookA_symmDiff_le`; tightness `lookahead_tight_card`, `lookahead_tight_residual` | exact (`Finset` formulation, `[Fintype α]`) |
| Prop 6.3 | Planning | (a) `abs_planValue_sub_le`, per plan `abs_planReturn_sub_le`, sup step `abs_sSup_image_sub_le`; (b) `planAgree_of_resAgree`, `exists_plan_detect`; (c) `abs_planValue_sub_le_of_reward_eq`, `Process.abs_planValue_sub_le_of_eps`, `pow_mul_inv_eq_div`; (d) `countdown_gap`, `countdown_resAgree`, `countdown_separates` | variant: `N_Π` enters as the hypothesis "admissibility agrees on `Π` up to step `K`" and the bound is stated at `K = N_Π − 1` (for `N_Π = ∞` it holds for every `K`); `Δ_t` is any bound on reward differences along `Π`; full `tsum`/`sSup` version |
| Prop 6.4 | — | not formalized | stochastic streams |
| Lemma 7.1 | Certificates | `mem_iff_no_minNonMember_subset`, `minNonMembers_isAntichain`, `exists_minNonMember_subset` | exact |
| Rem 7.2 | — | not formalized | immediate from definitions |
| Prop 7.3 | Certificates | `card_minNonMembers_le_sperner`, `sperner_tight_of_pos` | exact |
| Lemma 7.4 | Certificates | `shatters_iff_mem`, `vcDim_eq_dim` | exact (Mathlib's `Finset.Shatters`, `Finset.vcDim`) |
| Prop 7.5 | Certificates | `card_le_dim_succ_of_mem_minNonMembers`, `card_minNonMembers_le`, `card_minNonMembers_le_of_dim_le`, `card_le_sum_choose`, `dim_bound_tight_of_pos` | exact (rank = `K.sup card`); the "rank exactly `r`" remark is not formalized |
| Def 8.1 | Nondet | `UPres`, `UPres.Reach`, `UPres.safe`, `UPres.IsExact`, `UPres.Iso` | variant: states are any type with `DecidableEq`; `Fintype` is assumed where needed |
| Obs 8.2 | Nondet | `UPres.isExact_iff_accepts` | first sentence only; the NFA-size remark (Receipt R5) is not formalized |
| Lemma 8.3 | Nondet | `UPres.IsExact.resEquiv_of_Reach_eq`, `UPres.IsExact.card_quotient_le` | exact |
| Lemma 8.4 | Nondet | `UPres.IsExact.card_ge_of_fooling` | exact |
| Prop 8.5 | Nondet | `noBB_card_ge_three`, `noBB_index`, `Qκ_exact`, `Qalt_exact`, `Qκ_not_iso_Qalt`, `noBB_min_universal_size` | exact, except the exhaustive count (328 exact, 164 classes), which is not formalized |
| Thm 8.6 | Succinct | (a) `Vn_index`, `σn_eq_iff_resEquiv`; (b) `Un_exact`, `Vn_card_ge`, `Vn_min_universal_size`, `bad_snoc` | exact for all `n ≥ 2` |
| Prop 8.7 | — | not formalized | HMM realizations |
