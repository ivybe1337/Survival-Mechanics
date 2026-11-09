/-
Copyright (c) 2026 Joshua Matthew Carter. Released under the MIT-0 license.
Authors: Joshua Matthew Carter
-/
import LikelyAllowed.Predictive

/-!
# §6 Decisions (Paper Prop 6.1)
-/

namespace LikelyAllowed

universe u v w

variable {α : Type u}

/-- Paper §6. The feasible set `A(h) = {e | R_V(he) ≠ ∅} = {e | ∃ z, V(hez) = 1}`. -/
def feasible (V : List α → Bool) (h : List α) : Set α := {e | ∃ z, V (h ++ e :: z) = true}

theorem feasible_eq_resSet_nonempty (V : List α → Bool) (h : List α) :
    feasible V h = {e | (resSet V (h ++ [e])).Nonempty} := by
  ext e
  simp [feasible, resSet, Set.Nonempty]

/-- Paper Prop 6.1(a) (T13a). `A(h)` depends only on `κ(h)`. -/
theorem feasible_eq_of_resEquiv {V : List α → Bool} {h h' : List α} (H : ResEquiv V h h') :
    feasible V h = feasible V h' := by
  ext e
  simp only [feasible, Set.mem_ofPred_eq]
  exact exists_congr fun z => by rw [H (e :: z)]

/-- The argmax set `argmax_{e ∈ A} r(e)`. -/
def argmaxSet {β : Type v} [Preorder β] (A : Set α) (r : α → β) : Set α :=
  {e | e ∈ A ∧ ∀ e' ∈ A, r e' ≤ r e}

section Abstract

variable {S : Type w} {β : Type v}

/-- Paper Prop 6.1(b) (T13b), abstract form. Let `s` be a statistic refining `κ`
(e.g. `J`) and let the reward factor through it, `r(h,e) = r̃(s(h), e)`. Then the argmax over the
feasible set depends only on `s(h)`. -/
theorem argmax_eq_of_stat [Preorder β] (V : List α → Bool) (s : List α → S)
    (hs : ∀ h h', s h = s h' → ResEquiv V h h') (r : List α → α → β) (rt : S → α → β)
    (hr : ∀ h e, r h e = rt (s h) e) {h h' : List α} (hhh : s h = s h') :
    argmaxSet (feasible V h) (r h) = argmaxSet (feasible V h') (r h') := by
  have e1 : r h = r h' := funext fun e => by rw [hr, hr, hhh]
  rw [feasible_eq_of_resEquiv (hs h h' hhh), e1]

/-- Paper Prop 6.1(c): the `n`-step value of a policy `π`, with `⊥` (`none`) at
dead histories: `V⁰ = 0`, `V^{n+1}(h) = r(h, π h) + Vⁿ(h π(h))` if `A(h) ≠ ∅`, and `⊥` otherwise. -/
noncomputable def policyValue (V : List α → Bool) (π : List α → α) (r : List α → α → ℝ) :
    ℕ → List α → Option ℝ
  | 0, _ => some 0
  | n + 1, h =>
    open Classical in
    if (feasible V h).Nonempty then
      (policyValue V π r n (h ++ [π h])).map (fun v => r h (π h) + v)
    else none

/-- Paper Prop 6.1(c) (T17a, T18), abstract form. Let `s` be a right-congruent
statistic refining `κ`, and let the policy and reward factor through `s`. Then `s(h) = s(h') ⇒
Vⁿ(h) = Vⁿ(h')` for all `n`. (No feasibility hypothesis on `π` is needed for this invariance.) -/
theorem policyValue_eq_of_stat (V : List α → Bool) (s : List α → S)
    (hs : ∀ h h', s h = s h' → ResEquiv V h h')
    (hsr : ∀ h h' e, s h = s h' → s (h ++ [e]) = s (h' ++ [e]))
    (π : List α → α) (πt : S → α) (hπ : ∀ h, π h = πt (s h))
    (r : List α → α → ℝ) (rt : S → α → ℝ) (hr : ∀ h e, r h e = rt (s h) e) (n : ℕ) :
    ∀ {h h' : List α}, s h = s h' → policyValue V π r n h = policyValue V π r n h' := by
  induction n with
  | zero => intro h h' _; rfl
  | succ n ih =>
    intro h h' hhh
    have hA := feasible_eq_of_resEquiv (hs h h' hhh)
    have hπ' : π h = π h' := by rw [hπ, hπ, hhh]
    have hr' : r h (π h) = r h' (π h') := by rw [hπ', hr, hr, hhh]
    have hnext := ih (hsr h h' (π h) hhh)
    simp only [policyValue, hr', ← hπ', hnext]
    by_cases hne : (feasible V h).Nonempty
    · have hne' : (feasible V h').Nonempty := hA ▸ hne
      simp only [hne, hne', ↓reduceIte]
    · have hne' : ¬ (feasible V h').Nonempty := hA ▸ hne
      simp only [hne, hne', ↓reduceIte]

end Abstract

/-! ### Instantiation at the joint state `J` -/

namespace Process

variable [Fintype α] (P : Process α) (V : List α → Bool)

/-- The class map `J : h ↦ [h]_J`. -/
def J (h : List α) : Quotient (P.jSetoid V) := Quotient.mk _ h

theorem J_eq_iff {h h' : List α} : P.J V h = P.J V h' ↔ P.JEquiv V h h' :=
  ⟨Quotient.exact, fun H => Quotient.sound H⟩

/-- Paper Prop 6.1(b) for `J`: if `r(h,e) = r̃(J(h), e)` then `argmax_{e ∈ A(h)}
r(h,e)` depends only on `J(h)`. -/
theorem argmax_eq_of_jEquiv {β : Type v} [Preorder β] (r : List α → α → β)
    (rt : Quotient (P.jSetoid V) → α → β) (hr : ∀ h e, r h e = rt (P.J V h) e)
    {h h' : List α} (hJ : P.JEquiv V h h') :
    argmaxSet (feasible V h) (r h) = argmaxSet (feasible V h') (r h') :=
  argmax_eq_of_stat V (P.J V) (fun _ _ H => ((P.J_eq_iff V).mp H).2) r rt hr
    ((P.J_eq_iff V).mpr hJ)

/-- Paper Prop 6.1(c) for `J`: if `π = π̃ ∘ J` and `r(h,e) = r̃(J(h), e)` then
`J(h) = J(h') ⇒ Vⁿ(h) = Vⁿ(h')` for all `n`; no support hypothesis is needed (Lemma 2.11). -/
theorem policyValue_eq_of_jEquiv (π : List α → α) (πt : Quotient (P.jSetoid V) → α)
    (hπ : ∀ h, π h = πt (P.J V h)) (r : List α → α → ℝ) (rt : Quotient (P.jSetoid V) → α → ℝ)
    (hr : ∀ h e, r h e = rt (P.J V h) e) (n : ℕ) {h h' : List α} (hJ : P.JEquiv V h h') :
    policyValue V π r n h = policyValue V π r n h' :=
  policyValue_eq_of_stat V (P.J V) (fun _ _ H => ((P.J_eq_iff V).mp H).2)
    (fun _ _ e H => (P.J_eq_iff V).mpr (P.jEquiv_rightCongr V _ _ e ((P.J_eq_iff V).mp H)))
    π πt hπ r rt hr n ((P.J_eq_iff V).mpr hJ)

end Process

end LikelyAllowed
