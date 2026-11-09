/-
Copyright (c) 2026 Joshua Matthew Carter. Released under the MIT-0 license.
Authors: Joshua Matthew Carter
-/
import LikelyAllowed.Conditioned
import LikelyAllowed.Moore
import LikelyAllowed.ShortFutures

/-!
# Paper Theorem 5.4: survival-aware prediction is exactly the joint state

For histories all of whose continuations have positive probability, the survival-aware forecast
`σ(h) = (P_h, (S_n(h))_n, (Q_n(·|h))_n)` determines `J(h)` (part (a)); for finite-dimensional
processes and finite-index `V` a finite horizon suffices (part (b)); positivity cannot be
dropped (part (c)).
-/

namespace LikelyAllowed

open Finset

universe u

variable {α : Type u} [Fintype α]

namespace Process

variable (P : Process α) (V : List α → Bool)

theorem pred_nonneg (h z : List α) : 0 ≤ P.pred h z :=
  div_nonneg (P.p_nonneg _) (P.p_nonneg _)

theorem bit_nonneg (b : Bool) : 0 ≤ bit b := by unfold bit; split <;> norm_num

theorem survProb_nonneg (n : ℕ) (h : List α) : 0 ≤ P.survProb V n h :=
  Finset.sum_nonneg fun z _ => mul_nonneg (P.pred_nonneg h z) (bit_nonneg _)

/-- All continuations of `h` have positive probability. -/
def AllPos (h : List α) : Prop := ∀ z, P.p (h ++ z) ≠ 0

theorem pred_pos {h : List α} (hh : P.AllPos h) (z : List α) : 0 < P.pred h z := by
  have h0 : P.p h ≠ 0 := by simpa using hh []
  exact div_pos (lt_of_le_of_ne (P.p_nonneg _) (Ne.symm (hh z)))
    (lt_of_le_of_ne (P.p_nonneg _) (Ne.symm h0))

/-- Paper Thm 5.4 (proof of (a)): under positivity, `V(hz) = 1` iff `S_{|z|}(h) > 0` and
`Q_{|z|}(z|h) > 0`. -/
theorem survives_iff {h : List α} (hh : P.AllPos h) (z : List α) :
    V (h ++ z) = true ↔ 0 < P.survProb V z.length h ∧ 0 < P.condLaw V z.length h z := by
  have hp := P.pred_pos hh z
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

/-- Paper Thm 5.4 (κ half, any horizon `H`): under positivity, agreement of `S_n` and `Q_n` for
`n ≤ H` gives agreement of the residuals on all words of length `≤ H`. -/
theorem lenTest_of_forecasts_eq {h h' : List α} (hh : P.AllPos h) (hh' : P.AllPos h') (H : ℕ)
    (hS : ∀ n ≤ H, P.survProb V n h = P.survProb V n h')
    (hQ : ∀ n ≤ H, ∀ z ∈ words α n, P.condLaw V n h z = P.condLaw V n h' z) :
    LenTest V H h h' := by
  intro z hz
  have hz' : z.length ≤ H := hz
  rw [Bool.eq_iff_iff, P.survives_iff V hh, P.survives_iff V hh',
    hS _ hz', hQ _ hz' z (mem_words.mpr rfl)]

/-- Paper Thm 5.4(a), "only if": under positivity, `σ(h) = σ(h') ⇒ J(h) = J(h')`.
(Monotonicity of `V` is not needed.) -/
theorem jEquiv_of_forecasts_eq {h h' : List α} (hh : P.AllPos h) (hh' : P.AllPos h')
    (hP : P.pred h = P.pred h')
    (hS : ∀ n, P.survProb V n h = P.survProb V n h')
    (hQ : ∀ n, ∀ z ∈ words α n, P.condLaw V n h z = P.condLaw V n h' z) :
    P.JEquiv V h h' := by
  refine ⟨Or.inr ⟨by simpa using hh [], by simpa using hh' [], fun z => congrFun hP z⟩, ?_⟩
  intro z
  exact P.lenTest_of_forecasts_eq V hh hh' z.length (fun n _ => hS n)
    (fun n _ => hQ n) z (show z.length ≤ z.length from le_rfl)

/-- Paper Thm 5.4(a): under positivity, `σ(h) = σ(h') ⇔ J(h) = J(h')`. -/
theorem forecasts_eq_iff_jEquiv {h h' : List α} (hh : P.AllPos h) (hh' : P.AllPos h') :
    (P.pred h = P.pred h' ∧ (∀ n, P.survProb V n h = P.survProb V n h') ∧
        ∀ n, ∀ z ∈ words α n, P.condLaw V n h z = P.condLaw V n h' z) ↔
      P.JEquiv V h h' := by
  have h0 : P.p h ≠ 0 := by simpa using hh []
  constructor
  · rintro ⟨hP, hS, hQ⟩
    exact P.jEquiv_of_forecasts_eq V hh hh' hP hS hQ
  · intro hJ
    exact ⟨P.pred_eq_of_epsEquiv hJ.1 h0, fun n => P.survProb_eq_of_jEquiv V n hJ h0,
      fun n _ _ => P.condLaw_eq_of_jEquiv V n hJ h0 _⟩

/-- Paper Thm 5.4(b), κ half: if `ind(V) = k < ∞` and `H ≥ k - 2`, then under positivity
agreement of `S_n, Q_n` for `n ≤ H` gives `h ~_V h'`. -/
theorem resEquiv_of_truncated_forecasts_eq [Finite (Quotient (resSetoid V))] {h h' : List α}
    (hh : P.AllPos h) (hh' : P.AllPos h') {H : ℕ}
    (hH : Nat.card (Quotient (resSetoid V)) - 2 ≤ H)
    (hS : ∀ n ≤ H, P.survProb V n h = P.survProb V n h')
    (hQ : ∀ n ≤ H, ∀ z ∈ words α n, P.condLaw V n h z = P.condLaw V n h' z) :
    ResEquiv V h h' := by
  have hT := P.lenTest_of_forecasts_eq V hh hh' H hS hQ
  by_cases hk : 2 ≤ Nat.card (Quotient (resSetoid V))
  · exact (resEquiv_iff_lenTest hk h h').mpr (hT.anti hH)
  · have : Subsingleton (Quotient (resSetoid V)) :=
      Finite.card_le_one_iff_subsingleton.mp (by omega)
    exact Quotient.exact (Subsingleton.elim (Quotient.mk (resSetoid V) h) (Quotient.mk _ h'))

/-- Paper Thm 5.4(b): if `p` has a linear representation of dimension `m`, `ind(V) = k < ∞`,
and `H ≥ max(k - 2, m - 1)`, then under positivity the truncated forecast `σ_H` determines `J`:
`σ_H(h) = σ_H(h') ⇔ J(h) = J(h')`. -/
theorem truncated_forecasts_eq_iff_jEquiv [Finite (Quotient (resSetoid V))] (L : LinRep P)
    {h h' : List α} (hh : P.AllPos h) (hh' : P.AllPos h') {H : ℕ}
    (hHk : Nat.card (Quotient (resSetoid V)) - 2 ≤ H) (hHm : L.dim - 1 ≤ H) :
    ((∀ z : List α, z.length ≤ H → P.pred h z = P.pred h' z) ∧
        (∀ n ≤ H, P.survProb V n h = P.survProb V n h') ∧
        ∀ n ≤ H, ∀ z ∈ words α n, P.condLaw V n h z = P.condLaw V n h' z) ↔
      P.JEquiv V h h' := by
  have h0 : P.p h ≠ 0 := by simpa using hh []
  have h0' : P.p h' ≠ 0 := by simpa using hh' []
  constructor
  · rintro ⟨hP, hS, hQ⟩
    refine ⟨(L.epsEquiv_iff_short h0 h0').mpr fun z hz => hP z (hz.trans hHm), ?_⟩
    exact P.resEquiv_of_truncated_forecasts_eq V hh hh' hHk hS hQ
  · intro hJ
    exact ⟨fun z _ => congrFun (P.pred_eq_of_epsEquiv hJ.1 h0) z,
      fun n _ => P.survProb_eq_of_jEquiv V n hJ h0,
      fun n _ _ _ => P.condLaw_eq_of_jEquiv V n hJ h0 _⟩

end Process

/-! ### Paper Theorem 5.4(c): positivity cannot be dropped -/

/-- The process that emits `a = false` forever. -/
noncomputable def allAProcess : Process Bool where
  p w := if w.all (fun x => !x) then 1 else 0
  p_nil := by simp
  p_nonneg w := by split <;> norm_num
  p_sum w := by
    rw [Fintype.sum_bool]
    by_cases hw : w.all (fun x => !x) = true <;> simp [List.all_append, hw]

/-- `V(w) = 0` iff `w` begins with `ab`. -/
def startsAB : List Bool → Bool
  | false :: true :: _ => true
  | _ => false

/-- The admissibility rule of Paper Thm 5.4(c). -/
def Vab (w : List Bool) : Bool := !startsAB w

theorem allA_p_cons_false (z : List Bool) :
    allAProcess.p (false :: z) = allAProcess.p z := by
  simp [allAProcess]

theorem allA_p_nil : allAProcess.p [] = 1 := allAProcess.p_nil

theorem allA_p_false : allAProcess.p [false] = 1 := by
  rw [allA_p_cons_false, allA_p_nil]

/-- Paper Thm 5.4(c): `κ(Λ) ≠ κ(a)`. -/
theorem Vab_not_resEquiv : ¬ ResEquiv Vab [] [false] := by
  intro H
  have := H [true]
  simp [Vab, startsAB] at this

/-- Paper Thm 5.4(c): the positivity hypothesis fails (from `Λ`, `b` has probability `0`). -/
theorem allA_not_allPos : ¬ allAProcess.AllPos [] := by
  intro H
  exact H [true] (by simp [allAProcess])

theorem allA_pred_eq : allAProcess.pred [] = allAProcess.pred [false] := by
  funext z
  simp only [Process.pred, List.nil_append, allA_p_nil, List.cons_append, allA_p_cons_false]

theorem allA_term_eq (z : List Bool) :
    allAProcess.p z * bit (Vab z) = allAProcess.p z * bit (Vab (false :: z)) := by
  by_cases hp : allAProcess.p z = 0
  · simp [hp]
  · have hall : z.all (fun x => !x) = true := by
      by_contra hc
      have hc' : z.all (fun x => !x) = false := Bool.eq_false_iff.mpr hc
      exact hp (by simp only [allAProcess, hc', Bool.false_eq_true, ↓reduceIte])
    have hV : Vab z = true ∧ Vab (false :: z) = true := by
      match z, hall with
      | [], _ => exact ⟨rfl, rfl⟩
      | [x], hx => simp_all [Vab, startsAB]
      | x :: y :: w, hx =>
        simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hx
        obtain ⟨rfl, rfl, -⟩ := hx
        exact ⟨rfl, rfl⟩
    rw [hV.1, hV.2]

/-- Paper Thm 5.4(c): the survival probabilities from `Λ` and `a` agree at every horizon. -/
theorem allA_survProb_eq (n : ℕ) :
    allAProcess.survProb Vab n [] = allAProcess.survProb Vab n [false] := by
  unfold Process.survProb
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← allA_pred_eq]
  simp only [Process.pred, List.nil_append, allA_p_nil, div_one, List.cons_append]
  exact allA_term_eq z

/-- Paper Thm 5.4(c): the conditioned forecasts from `Λ` and `a` agree at every horizon. -/
theorem allA_condLaw_eq (n : ℕ) (z : List Bool) :
    allAProcess.condLaw Vab n [] z = allAProcess.condLaw Vab n [false] z := by
  unfold Process.condLaw
  rw [← allA_survProb_eq, ← allA_pred_eq]
  simp only [Process.pred, List.nil_append, allA_p_nil, div_one, List.cons_append]
  rw [allA_term_eq z]

/-- Paper Thm 5.4(c): `σ(Λ) = σ(a)` but `J(Λ) ≠ J(a)`. -/
theorem positivity_necessary :
    allAProcess.pred [] = allAProcess.pred [false] ∧
      (∀ n, allAProcess.survProb Vab n [] = allAProcess.survProb Vab n [false]) ∧
      (∀ n z, allAProcess.condLaw Vab n [] z = allAProcess.condLaw Vab n [false] z) ∧
      ¬ allAProcess.JEquiv Vab [] [false] :=
  ⟨allA_pred_eq, allA_survProb_eq, allA_condLaw_eq, fun h => Vab_not_resEquiv h.2⟩

end LikelyAllowed
