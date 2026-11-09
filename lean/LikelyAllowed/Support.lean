/-
Copyright (c) 2026 Joshua Matthew Carter. Released under Apache 2.0 license.
Authors: Joshua Matthew Carter
-/
import LikelyAllowed.Exactness
import Mathlib.Algebra.BigOperators.Field

/-!
# Paper Corollary 5.6: what the forecasts see without full support

The supported residual `R_V^p(h) = {z | P_h(z) > 0, V(hz) = 1}` and the supported joint state
`J_p = (ε, R_V^p)`. Without any positivity hypothesis, the survival data
`Ψ(h) = (P_h, (S_n(h))_n, (Q_n(·|h))_n)` of two supported histories agree iff their supported
joint states agree (Paper Cor 5.6); `Ψ` depends only on `J_p` (the support form of Paper
Prop 5.3); rules that agree on the support give the same survival data, so the forecasts say
nothing about `R_V(h)` off the support (Paper Cor 5.6, second sentence); and the survival
probabilities obey a one-step recursion on the product of a predictive machine and the
residual machine.
-/

namespace LikelyAllowed

open Finset

universe u

variable {α : Type u} [Fintype α]

/-! ### Sums over `Σ^{n+1}` split by the first letter -/

/-- `Σ_{z ∈ Σ^{n+1}} f(z) = Σ_a Σ_{y ∈ Σ^n} f(a y)`. -/
theorem sum_words_succ {M : Type*} [AddCommMonoid M] (f : List α → M) (n : ℕ) :
    ∑ z ∈ words α (n + 1), f z = ∑ a, ∑ y ∈ words α n, f (a :: y) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun x _ => x.1 :: x.2) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_product] at hx
    rw [mem_words, List.length_cons, mem_words.mp hx.2]
  · intro x _ y _ hxy
    simp only [List.cons.injEq] at hxy
    exact Prod.ext hxy.1 hxy.2
  · intro z hz
    rw [mem_words] at hz
    match z, hz with
    | a :: y, hy =>
      exact ⟨(a, y), Finset.mem_product.mpr ⟨Finset.mem_univ _,
        mem_words.mpr (by simpa using hy)⟩, rfl⟩
  · intro _ _
    rfl

namespace Process

variable (P : Process α) (V : List α → Bool)

/-! ### The supported residual and the supported joint state -/

/-- Paper Cor 5.6. The supported residual
`R_V^p(h) = {z | P_h(z) > 0, V(hz) = 1}`: the admissible continuations the process can produce.
(`P_h(z) ≥ 0`, so `P_h(z) ≠ 0` is `P_h(z) > 0`.) -/
def resP (h : List α) : Set (List α) := {z | P.pred h z ≠ 0 ∧ V (h ++ z) = true}

/-- Paper Cor 5.6. The supported joint equivalence `h ~_{J,p} h'`: `h ~_ε h'` and
`R_V^p(h) = R_V^p(h')`. -/
def JpEquiv (h h' : List α) : Prop := P.EpsEquiv h h' ∧ P.resP V h = P.resP V h'

theorem pred_eq_zero_of_null {h : List α} (hh : P.p h = 0) (z : List α) : P.pred h z = 0 := by
  simp [pred, hh]

theorem pred_ne_zero_iff {h : List α} (hh : P.p h ≠ 0) (z : List α) :
    P.pred h z ≠ 0 ↔ P.p (h ++ z) ≠ 0 := by
  simp [pred, hh]

theorem pred_pos_of_ne_zero {h z : List α} (hz : P.pred h z ≠ 0) : 0 < P.pred h z :=
  lt_of_le_of_ne (P.pred_nonneg h z) (Ne.symm hz)

/-- `R_V^p(h) = R_V(h) ∩ {z | P_h(z) > 0}`. -/
theorem resP_eq_inter (h : List α) : P.resP V h = resSet V h ∩ {z | P.pred h z ≠ 0} := by
  ext z
  simp only [resP, resSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
  exact and_comm

/-- On the support, `z ∈ R_V^p(h)` iff `p(hz) > 0` and `V(hz) = 1`. -/
theorem mem_resP_iff {h : List α} (hh : P.p h ≠ 0) (z : List α) :
    z ∈ P.resP V h ↔ P.p (h ++ z) ≠ 0 ∧ V (h ++ z) = true := by
  simp only [resP, Set.mem_ofPred_eq, P.pred_ne_zero_iff hh]

/-- A null history has no supported continuations. -/
theorem resP_of_null {h : List α} (hh : P.p h = 0) : P.resP V h = ∅ := by
  ext z
  simp [resP, P.pred_eq_zero_of_null hh]

/-- Under full support from `h`, `R_V^p(h) = R_V(h)`. -/
theorem resP_eq_resSet_of_allPos {h : List α} (hh : P.AllPos h) :
    P.resP V h = resSet V h := by
  rw [resP_eq_inter]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_iff_left_iff_imp]
  exact fun _ => (P.pred_pos hh z).ne'

/-- `~_{J,p}` is an equivalence relation. -/
theorem jpEquiv_equivalence : Equivalence (P.JpEquiv V) where
  refl h := ⟨P.epsEquiv_equivalence.refl h, rfl⟩
  symm H := ⟨P.epsEquiv_equivalence.symm H.1, H.2.symm⟩
  trans H H' := ⟨P.epsEquiv_equivalence.trans H.1 H'.1, H.2.trans H'.2⟩

/-- `R_V^p(hz)` is read off `R_V^p(h)` on the support: `y ∈ R_V^p(hz) ⇔ zy ∈ R_V^p(h)`. -/
theorem mem_resP_append_iff {h z : List α} (hz : P.p (h ++ z) ≠ 0) (y : List α) :
    y ∈ P.resP V (h ++ z) ↔ z ++ y ∈ P.resP V h := by
  have hh : P.p h ≠ 0 := fun h0 => hz (P.p_append_eq_zero h0 z)
  rw [P.mem_resP_iff V hz, P.mem_resP_iff V hh, List.append_assoc]

/-- `~_{J,p}` is a right congruence. -/
theorem jpEquiv_rightCongr : RightCongr (P.JpEquiv V) := by
  intro h h' e H
  refine ⟨P.epsEquiv_rightCongr _ _ e H.1, ?_⟩
  rcases P.epsEquiv_rightCongr _ _ e H.1 with ⟨h1, h2⟩ | ⟨h1, h2, -⟩
  · rw [P.resP_of_null V h1, P.resP_of_null V h2]
  · ext y
    rw [P.mem_resP_append_iff V h1, P.mem_resP_append_iff V h2, H.2]

/-- `h ~_J h' ⇒ h ~_{J,p} h'`: `J` determines `J_p`. -/
theorem jpEquiv_of_jEquiv {h h' : List α} (H : P.JEquiv V h h') : P.JpEquiv V h h' := by
  refine ⟨H.1, ?_⟩
  rcases H.1 with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · rw [P.resP_of_null V h1, P.resP_of_null V h2]
  · ext z
    simp only [resP, Set.mem_ofPred_eq, pred, h3 z, H.2 z]

/-! ### Paper Prop 5.3, support form -/

/-- The key identity: on the support, `h ~_{J,p} h'` gives
`P_h(z) V(hz) = P_{h'}(z) V(h'z)` for every `z`. -/
theorem pred_mul_bit_eq_of_jpEquiv {h h' : List α} (H : P.JpEquiv V h h') (hh : P.p h ≠ 0)
    (z : List α) : P.pred h z * bit (V (h ++ z)) = P.pred h' z * bit (V (h' ++ z)) := by
  have hP := P.pred_eq_of_epsEquiv H.1 hh
  rw [← hP]
  by_cases hz : P.pred h z = 0
  · simp [hz]
  · have hz' : P.pred h' z ≠ 0 := hP ▸ hz
    have hV : V (h ++ z) = V (h' ++ z) := by
      rw [Bool.eq_iff_iff]
      have := congrArg (fun S => z ∈ S) H.2
      simp only [resP, Set.mem_ofPred_eq, eq_iff_iff] at this
      exact ⟨fun hv => (this.mp ⟨hz, hv⟩).2, fun hv => (this.mpr ⟨hz', hv⟩).2⟩
    rw [hV]

/-- Paper Prop 5.3 (support form), general finite form: for a finite set `Z` of
continuations and any `g`, the sum `Σ_{z∈Z} P_h(z) g(z, V(hz))` depends only on `J_p(h)`. -/
theorem sum_pred_mul_eq_of_jpEquiv (Z : Finset (List α)) (g : List α → Bool → ℝ)
    {h h' : List α} (H : P.JpEquiv V h h') (hh : P.p h ≠ 0) :
    ∑ z ∈ Z, P.pred h z * g z (V (h ++ z)) = ∑ z ∈ Z, P.pred h' z * g z (V (h' ++ z)) := by
  have hP := P.pred_eq_of_epsEquiv H.1 hh
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : P.pred h z = 0
  · rw [hz, ← congrFun hP z, hz, zero_mul, zero_mul]
  · have e := P.pred_mul_bit_eq_of_jpEquiv V H hh z
    rw [← congrFun hP z] at e ⊢
    have hV : V (h ++ z) = V (h' ++ z) := by
      have e' := mul_left_cancel₀ hz e
      cases h1 : V (h ++ z) <;> cases h2 : V (h' ++ z) <;> simp_all [bit]
    rw [hV]

/-- Paper Prop 5.3 (support form): `S_n(h)` depends only on `J_p(h)`. -/
theorem survProb_eq_of_jpEquiv (n : ℕ) {h h' : List α} (H : P.JpEquiv V h h')
    (hh : P.p h ≠ 0) : P.survProb V n h = P.survProb V n h' :=
  P.sum_pred_mul_eq_of_jpEquiv V (words α n) (fun _ b => bit b) H hh

/-- Paper Prop 5.3 (support form): `Q_n(·|h)` depends only on `J_p(h)`. -/
theorem condLaw_eq_of_jpEquiv (n : ℕ) {h h' : List α} (H : P.JpEquiv V h h')
    (hh : P.p h ≠ 0) (z : List α) : P.condLaw V n h z = P.condLaw V n h' z := by
  unfold condLaw
  rw [P.survProb_eq_of_jpEquiv V n H hh, P.pred_mul_bit_eq_of_jpEquiv V H hh z]

/-- Paper Prop 5.3 (support form, `n = ∞`), for any limit functional `lim`. -/
theorem survInf_eq_of_jpEquiv (lim : (ℕ → ℝ) → ℝ) {h h' : List α} (H : P.JpEquiv V h h')
    (hh : P.p h ≠ 0) : P.survInf V lim h = P.survInf V lim h' := by
  unfold survInf
  congr 1
  funext n
  exact P.survProb_eq_of_jpEquiv V n H hh

/-- Paper Prop 5.3 (support form, `n = ∞`): `Q_∞(·|h)` depends only on `J_p(h)`. -/
theorem condLawInf_eq_of_jpEquiv (lim : (ℕ → ℝ) → ℝ) {h h' : List α}
    (H : P.JpEquiv V h h') (hh : P.p h ≠ 0) (z : List α) :
    P.condLawInf V lim h z = P.condLawInf V lim h' z := by
  unfold condLawInf
  have hpred := congrFun (P.pred_eq_of_epsEquiv H.1 hh) z
  rw [P.survInf_eq_of_jpEquiv V lim H hh, ← hpred]
  by_cases hz : P.p (h ++ z) = 0
  · simp [pred, hz]
  · rw [P.survInf_eq_of_jpEquiv V lim ((P.jpEquiv_rightCongr V).append H z) hz]

/-- Paper Prop 5.3 (support form): for `h ∈ Supp p`, `Ψ(h)` is a function of `J_p(h)`, and therefore
of `J(h)`. -/
theorem sufficiency_support {h h' : List α} (hh : P.p h ≠ 0) (H : P.JpEquiv V h h') :
    P.pred h = P.pred h' ∧ (∀ n, P.survProb V n h = P.survProb V n h') ∧
      ∀ n z, P.condLaw V n h z = P.condLaw V n h' z :=
  ⟨P.pred_eq_of_epsEquiv H.1 hh, fun n => P.survProb_eq_of_jpEquiv V n H hh,
    fun n z => P.condLaw_eq_of_jpEquiv V n H hh z⟩

/-! ### Paper Cor 5.6 -/

/-- If `P_h(z) > 0`, then `V(hz) = 1` iff `S_{|z|}(h) > 0` and `Q_{|z|}(z|h) > 0`. -/
theorem survives_iff_of_pred_ne_zero {h z : List α} (hz : P.pred h z ≠ 0) :
    V (h ++ z) = true ↔ 0 < P.survProb V z.length h ∧ 0 < P.condLaw V z.length h z := by
  have hp := P.pred_pos_of_ne_zero hz
  constructor
  · intro hV
    have hterm : P.pred h z * bit (V (h ++ z)) ≤ P.survProb V z.length h :=
      Finset.single_le_sum (f := fun y => P.pred h y * bit (V (h ++ y)))
        (fun y _ => mul_nonneg (P.pred_nonneg h y) (bit_nonneg _)) (mem_words.mpr rfl)
    have hb : bit (V (h ++ z)) = 1 := by simp [bit, hV]
    rw [hb, mul_one] at hterm
    have hS : 0 < P.survProb V z.length h := lt_of_lt_of_le hp hterm
    refine ⟨hS, ?_⟩
    unfold condLaw
    rw [hb, mul_one]
    exact div_pos hp hS
  · rintro ⟨-, hQ⟩
    by_contra hV
    have hb : bit (V (h ++ z)) = 0 := by simp [bit, hV]
    unfold condLaw at hQ
    rw [hb, mul_zero, zero_div] at hQ
    exact lt_irrefl _ hQ

/-- Paper Cor 5.6, "only if". No positivity hypothesis. -/
theorem jpEquiv_of_forecasts_eq {h h' : List α} (hh : P.p h ≠ 0) (hh' : P.p h' ≠ 0)
    (hP : P.pred h = P.pred h')
    (hS : ∀ n, P.survProb V n h = P.survProb V n h')
    (hQ : ∀ n, ∀ z ∈ words α n, P.condLaw V n h z = P.condLaw V n h' z) :
    P.JpEquiv V h h' := by
  refine ⟨Or.inr ⟨hh, hh', fun z => congrFun hP z⟩, ?_⟩
  ext z
  simp only [resP, Set.mem_ofPred_eq, ← hP]
  constructor
  · rintro ⟨hz, hv⟩
    refine ⟨hz, ?_⟩
    have hz' : P.pred h' z ≠ 0 := hP ▸ hz
    rw [P.survives_iff_of_pred_ne_zero V hz'] at ⊢
    rw [P.survives_iff_of_pred_ne_zero V hz] at hv
    rw [← hS, ← hQ _ z (mem_words.mpr rfl)]
    exact hv
  · rintro ⟨hz, hv⟩
    refine ⟨hz, ?_⟩
    have hz' : P.pred h' z ≠ 0 := hP ▸ hz
    rw [P.survives_iff_of_pred_ne_zero V hz]
    rw [P.survives_iff_of_pred_ne_zero V hz'] at hv
    rw [hS, hQ _ z (mem_words.mpr rfl)]
    exact hv

/-- Paper Cor 5.6: for `h, h' ∈ Supp p`, with no positivity hypothesis,
`Ψ(h) = Ψ(h')` iff `J_p(h) = J_p(h')`. The data are packaged exactly as in
`forecasts_eq_iff_jEquiv`. -/
theorem forecasts_eq_iff_jpEquiv {h h' : List α} (hh : P.p h ≠ 0) (hh' : P.p h' ≠ 0) :
    (P.pred h = P.pred h' ∧ (∀ n, P.survProb V n h = P.survProb V n h') ∧
        ∀ n, ∀ z ∈ words α n, P.condLaw V n h z = P.condLaw V n h' z) ↔
      P.JpEquiv V h h' := by
  constructor
  · rintro ⟨hP, hS, hQ⟩
    exact P.jpEquiv_of_forecasts_eq V hh hh' hP hS hQ
  · intro H
    exact ⟨P.pred_eq_of_epsEquiv H.1 hh, fun n => P.survProb_eq_of_jpEquiv V n H hh,
      fun n z _ => P.condLaw_eq_of_jpEquiv V n H hh z⟩

/-- Paper Cor 5.6, last clause: under full support from `h` and `h'`, the
supported joint equivalence is the joint equivalence. -/
theorem jpEquiv_iff_jEquiv_of_allPos {h h' : List α} (hh : P.AllPos h) (hh' : P.AllPos h') :
    P.JpEquiv V h h' ↔ P.JEquiv V h h' := by
  unfold JpEquiv JEquiv
  rw [P.resP_eq_resSet_of_allPos V hh, P.resP_eq_resSet_of_allPos V hh',
    ← resEquiv_iff_resSet_eq]

/-- Paper Cor 5.6, full-support case: recovers `forecasts_eq_iff_jEquiv`. -/
theorem forecasts_eq_iff_jEquiv_via_support {h h' : List α} (hh : P.AllPos h)
    (hh' : P.AllPos h') :
    (P.pred h = P.pred h' ∧ (∀ n, P.survProb V n h = P.survProb V n h') ∧
        ∀ n, ∀ z ∈ words α n, P.condLaw V n h z = P.condLaw V n h' z) ↔
      P.JEquiv V h h' := by
  rw [P.forecasts_eq_iff_jpEquiv V (by simpa using hh []) (by simpa using hh' []),
    P.jpEquiv_iff_jEquiv_of_allPos V hh hh']

/-! ### Rules that agree on the support (Paper Cor 5.6) -/

/-- Two rules agree on the support of `p`. -/
def AgreeOnSupp (V V' : List α → Bool) : Prop := ∀ w, P.p w ≠ 0 → V w = V' w

theorem pred_mul_bit_eq_of_agree {V V' : List α → Bool} (hVV : P.AgreeOnSupp V V')
    (h z : List α) : P.pred h z * bit (V (h ++ z)) = P.pred h z * bit (V' (h ++ z)) := by
  by_cases hh : P.p h = 0
  · simp [P.pred_eq_zero_of_null hh]
  by_cases hz : P.p (h ++ z) = 0
  · simp [pred, hz]
  · rw [hVV _ hz]

/-- Paper Cor 5.6: if `V` and `V'` agree on `Supp p`, then `S_n` coincide at every history
(in particular every supported one). Monotonicity is not needed. -/
theorem survProb_eq_of_agree {V V' : List α → Bool} (hVV : P.AgreeOnSupp V V') (n : ℕ)
    (h : List α) : P.survProb V n h = P.survProb V' n h :=
  Finset.sum_congr rfl fun z _ => P.pred_mul_bit_eq_of_agree hVV h z

/-- Paper Cor 5.6: if `V` and `V'` agree on `Supp p`, then `Q_n(·|h)` coincide. -/
theorem condLaw_eq_of_agree {V V' : List α → Bool} (hVV : P.AgreeOnSupp V V') (n : ℕ)
    (h z : List α) : P.condLaw V n h z = P.condLaw V' n h z := by
  unfold condLaw
  rw [P.survProb_eq_of_agree hVV, P.pred_mul_bit_eq_of_agree hVV]

/-- Paper Cor 5.6: if `V` and `V'` agree on `Supp p`, then they have the same supported
residuals, hence the same supported joint state. -/
theorem resP_eq_of_agree {V V' : List α → Bool} (hVV : P.AgreeOnSupp V V') (h : List α) :
    P.resP V h = P.resP V' h := by
  by_cases hh : P.p h = 0
  · rw [P.resP_of_null V hh, P.resP_of_null V' hh]
  · ext z
    rw [P.mem_resP_iff V hh, P.mem_resP_iff V' hh]
    exact ⟨fun ⟨hz, hv⟩ => ⟨hz, hVV _ hz ▸ hv⟩, fun ⟨hz, hv⟩ => ⟨hz, (hVV _ hz).symm ▸ hv⟩⟩

theorem jpEquiv_iff_of_agree {V V' : List α → Bool} (hVV : P.AgreeOnSupp V V')
    (h h' : List α) : P.JpEquiv V h h' ↔ P.JpEquiv V' h h' := by
  unfold JpEquiv
  rw [P.resP_eq_of_agree hVV h, P.resP_eq_of_agree hVV h']

/-- Paper Cor 5.6, first sentence: rules that agree on `Supp p` give every history the same
survival data `Ψ`. -/
theorem blind_agree {V V' : List α → Bool} (hVV : P.AgreeOnSupp V V') (h : List α) :
    (∀ n, P.survProb V n h = P.survProb V' n h) ∧
      ∀ n z, P.condLaw V n h z = P.condLaw V' n h z :=
  ⟨fun n => P.survProb_eq_of_agree hVV n h, fun n z => P.condLaw_eq_of_agree hVV n h z⟩

/-! ### A one-step recursion for survival probabilities -/

/-- `P_h(xy) = P_h(x) P_{hx}(y)`, for every `h` (both sides vanish off the support). -/
theorem pred_cons (h : List α) (x : α) (y : List α) :
    P.pred h (x :: y) = P.pred h [x] * P.pred (h ++ [x]) y := by
  unfold pred
  have e : h ++ x :: y = h ++ [x] ++ y := by simp
  by_cases hx : P.p (h ++ [x]) = 0
  · rw [e, P.p_append_eq_zero hx y, hx]
    simp
  · have hh : P.p h ≠ 0 := fun h0 => hx (P.p_append_eq_zero h0 [x])
    rw [e]
    field_simp

/-- proof: summing `Q`-numerators over continuations starting with `x`,
`Σ_{y∈Σ^n} P_h(xy) V(hxy) = P_h(x) S_n(hx)`. -/
theorem sum_cons_eq (n : ℕ) (h : List α) (x : α) :
    ∑ y ∈ words α n, P.pred h (x :: y) * bit (V (h ++ x :: y)) =
      P.pred h [x] * P.survProb V n (h ++ [x]) := by
  unfold survProb
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [P.pred_cons, mul_assoc]
  simp

theorem survProb_zero {h : List α} (hh : P.p h ≠ 0) : P.survProb V 0 h = bit (V h) := by
  have hw : words α 0 = {[]} := by
    ext z
    simp [mem_words]
  simp [survProb, hw, pred, hh]

/-- proof: for monotone `V`,
`S_{n+1}(h) = V(h) Σ_x P_h(x) S_n(hx)`, for every `h`. -/
theorem survProb_succ (hV : AdmMonotone V) (n : ℕ) (h : List α) :
    P.survProb V (n + 1) h = bit (V h) * ∑ x, P.pred h [x] * P.survProb V n (h ++ [x]) := by
  have key : ∀ x, ∑ y ∈ words α n, P.pred h (x :: y) * bit (V (h ++ x :: y)) =
      bit (V h) * ∑ y ∈ words α n, P.pred h (x :: y) * bit (V (h ++ x :: y)) := by
    intro x
    cases hv : V h
    · simp only [bit, Bool.false_eq_true, ↓reduceIte, zero_mul]
      refine Finset.sum_eq_zero fun y _ => ?_
      have : V (h ++ x :: y) = false := by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        rw [hV h _ hc] at hv
        exact Bool.noConfusion hv
      simp [this]
    · simp [bit]
  unfold survProb
  rw [sum_words_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [key x, sum_cons_eq]
  rfl

/-- first-symbol marginal: `Σ_{y∈Σ^n} Q_{n+1}(xy|h) = P_h(x) S_n(hx) /
S_{n+1}(h)`. Monotonicity is not needed. -/
theorem condLaw_marginal (n : ℕ) (h : List α) (x : α) :
    ∑ y ∈ words α n, P.condLaw V (n + 1) h (x :: y) =
      P.pred h [x] * P.survProb V n (h ++ [x]) / P.survProb V (n + 1) h := by
  unfold condLaw
  rw [← Finset.sum_div, sum_cons_eq]

/-- the dynamic program on the product of a predictive machine
`(E, e₀, τ, π)` and a deterministic automaton `(K, k₀, λ, F)`:
`S̄₀(e,k) = [k ∈ F]`, `S̄_{n+1}(e,k) = [k ∈ F] Σ_x π(e,x) S̄_n(τ(e,x), λ(k,x))`. -/
noncomputable def combineS {E K : Type*} (τ : E → α → E) (π : E → α → ℝ) (lam : K → α → K)
    (F : K → Bool) : ℕ → E → K → ℝ
  | 0, _, k => bit (F k)
  | n + 1, e, k => bit (F k) * ∑ x, π e x * combineS τ π lam F n (τ e x) (lam k x)

/-- if `(E, e₀, τ, π)` is a predictive machine for `p` (on the support,
`P_h(x) = π(τ*(e₀,h), x)`) and `V(w) = [λ*(k₀,w) ∈ F]` is monotone, then
`S_n(h) = S̄_n(τ*(e₀,h), λ*(k₀,h))` for every supported `h`. -/
theorem survProb_eq_combineS {E K : Type*} (τ : E → α → E) (π : E → α → ℝ) (e₀ : E)
    (lam : K → α → K) (F : K → Bool) (k₀ : K)
    (hπ : ∀ h, P.p h ≠ 0 → ∀ x, P.pred h [x] = π (h.foldl τ e₀) x)
    (hVF : ∀ w, V w = F (w.foldl lam k₀)) (hV : AdmMonotone V) (n : ℕ) :
    ∀ h, P.p h ≠ 0 →
      P.survProb V n h = combineS τ π lam F n (h.foldl τ e₀) (h.foldl lam k₀) := by
  induction n with
  | zero =>
    intro h hh
    rw [P.survProb_zero V hh, combineS, hVF]
  | succ n ih =>
    intro h hh
    rw [P.survProb_succ V hV, combineS, hVF]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : P.p (h ++ [x]) = 0
    · have h1 : P.pred h [x] = 0 := by simp [pred, hx]
      rw [h1, ← hπ h hh x, h1, zero_mul, zero_mul]
    · rw [hπ h hh x, ih _ hx, List.foldl_append, List.foldl_append]
      rfl

/-- the first-symbol marginal in machine form: with `(e,k)` the pair of
states reached by the supported history `h`,
`Σ_y Q_{n+1}(xy|h) = π(e,x) S̄_n(τ(e,x), λ(k,x)) / S̄_{n+1}(e,k)`. -/
theorem condLaw_marginal_combineS {E K : Type*} (τ : E → α → E) (π : E → α → ℝ) (e₀ : E)
    (lam : K → α → K) (F : K → Bool) (k₀ : K)
    (hπ : ∀ h, P.p h ≠ 0 → ∀ x, P.pred h [x] = π (h.foldl τ e₀) x)
    (hVF : ∀ w, V w = F (w.foldl lam k₀)) (hV : AdmMonotone V) (n : ℕ) {h : List α}
    (hh : P.p h ≠ 0) (x : α) :
    ∑ y ∈ words α n, P.condLaw V (n + 1) h (x :: y) =
      π (h.foldl τ e₀) x * combineS τ π lam F n (τ (h.foldl τ e₀) x) (lam (h.foldl lam k₀) x) /
        combineS τ π lam F (n + 1) (h.foldl τ e₀) (h.foldl lam k₀) := by
  rw [P.condLaw_marginal, P.survProb_eq_combineS V τ π e₀ lam F k₀ hπ hVF hV (n + 1) h hh,
    ← hπ h hh x]
  by_cases hx : P.p (h ++ [x]) = 0
  · have h1 : P.pred h [x] = 0 := by simp [pred, hx]
    rw [h1, zero_mul, zero_mul]
  · rw [P.survProb_eq_combineS V τ π e₀ lam F k₀ hπ hVF hV n _ hx, List.foldl_append,
      List.foldl_append]
    rfl

end Process

/-! ### Example for Paper Cor 5.6 -/

/-- `Vab` (dies iff the word starts with `ab`) is monotone. -/
theorem Vab_admMonotone : AdmMonotone Vab := by
  intro h z hz
  match h, hz with
  | [], _ => rfl
  | [x], _ => cases x <;> rfl
  | true :: _ :: _, _ => rfl
  | false :: false :: _, _ => rfl
  | false :: true :: _, hz => simp [Vab, startsAB] at hz

/-- `Vab` and the rule `V' ≡ 1` agree on the support of the process that emits `a` forever. -/
theorem allA_agree : allAProcess.AgreeOnSupp Vab (fun _ => true) := by
  intro w hw
  have hall : w.all (fun x => !x) = true := by
    by_contra hc
    exact hw (by simp only [allAProcess, hc, Bool.false_eq_true, ↓reduceIte])
  match w, hall with
  | [], _ => rfl
  | [x], _ => cases x <;> rfl
  | x :: y :: w, hx =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hx
    obtain ⟨rfl, rfl, -⟩ := hx
    rfl

/-- Example for Paper Cor 5.6: `p` emits `a` forever, `V' ≡ 1`, and `V = Vab` dies iff the
word starts with `ab`. Both rules are monotone and agree on `Supp p`; `Ψ(Λ) = Ψ(a)` under both
rules, and the supported joint states of `Λ` and `a` coincide under both; yet under `V` the
continuation `b` is admissible after `Λ` and not after `a`, so `κ(Λ) ≠ κ(a)` for `V`, while
`κ(Λ) = κ(a)` for `V'`. -/
theorem blind_example :
    AdmMonotone Vab ∧ AdmMonotone (fun _ : List Bool => true) ∧
      allAProcess.AgreeOnSupp Vab (fun _ => true) ∧
      allAProcess.pred [] = allAProcess.pred [false] ∧
      (∀ n, allAProcess.survProb Vab n [] = allAProcess.survProb Vab n [false]) ∧
      (∀ n z, allAProcess.condLaw Vab n [] z = allAProcess.condLaw Vab n [false] z) ∧
      (∀ n, allAProcess.survProb (fun _ => true) n [] =
        allAProcess.survProb (fun _ => true) n [false]) ∧
      (∀ n z, allAProcess.condLaw (fun _ => true) n [] z =
        allAProcess.condLaw (fun _ => true) n [false] z) ∧
      allAProcess.JpEquiv Vab [] [false] ∧
      allAProcess.JpEquiv (fun _ => true) [] [false] ∧
      Vab ([] ++ [true]) = true ∧ Vab ([false] ++ [true]) = false ∧
      ¬ ResEquiv Vab [] [false] ∧ ResEquiv (fun _ : List Bool => true) [] [false] := by
  have hSV : ∀ n, allAProcess.survProb Vab n [] = allAProcess.survProb Vab n [false] :=
    allA_survProb_eq
  have hQV : ∀ n z, allAProcess.condLaw Vab n [] z = allAProcess.condLaw Vab n [false] z :=
    allA_condLaw_eq
  have hJp : allAProcess.JpEquiv Vab [] [false] :=
    (allAProcess.forecasts_eq_iff_jpEquiv Vab (by rw [allA_p_nil]; norm_num)
      (by rw [allA_p_false]; norm_num)).mp ⟨allA_pred_eq, hSV, fun n z _ => hQV n z⟩
  refine ⟨Vab_admMonotone, fun _ _ _ => rfl, allA_agree, allA_pred_eq, hSV, hQV, ?_, ?_,
    hJp, (allAProcess.jpEquiv_iff_of_agree allA_agree _ _).mp hJp, rfl, rfl,
    Vab_not_resEquiv, fun _ => rfl⟩
  · intro n
    rw [← allAProcess.survProb_eq_of_agree allA_agree,
      ← allAProcess.survProb_eq_of_agree allA_agree]
    exact hSV n
  · intro n z
    rw [← allAProcess.condLaw_eq_of_agree allA_agree,
      ← allAProcess.condLaw_eq_of_agree allA_agree]
    exact hQV n z

end LikelyAllowed
