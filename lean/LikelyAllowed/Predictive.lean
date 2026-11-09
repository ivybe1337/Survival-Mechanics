/-
Copyright (c) 2026 Joshua Matthew Carter. Released under the MIT-0 license.
Authors: Joshua Matthew Carter
-/
import LikelyAllowed.Joint
import LikelyAllowed.Canonical
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic

/-!
# Processes and predictive states (Paper Def 2.9, Def 2.10, Lemma 2.11, Def 2.13,
Cor 3.3, Prop 4.2)
-/

namespace LikelyAllowed

open Finset

universe u

variable {α : Type u} [Fintype α]

/-- Paper Def 2.9. A process: `p : Σ* → ℝ` with `p(Λ) = 1`, `p ≥ 0`, `p(w) = Σ_a
p(wa)`. -/
structure Process (α : Type u) [Fintype α] where
  /-- the word probabilities -/
  p : List α → ℝ
  p_nil : p [] = 1
  p_nonneg : ∀ w, 0 ≤ p w
  p_sum : ∀ w, p w = ∑ a, p (w ++ [a])

namespace Process

variable (P : Process α)

theorem p_snoc_le (w : List α) (a : α) : P.p (w ++ [a]) ≤ P.p w := by
  rw [P.p_sum w]
  exact Finset.single_le_sum (f := fun b => P.p (w ++ [b])) (fun b _ => P.p_nonneg _)
    (Finset.mem_univ a)

/-- Paper Def 2.9. `p(wz) ≤ p(w)`. -/
theorem p_append_le (w z : List α) : P.p (w ++ z) ≤ P.p w := by
  induction z generalizing w with
  | nil => simp
  | cons a z ih =>
    calc P.p (w ++ a :: z) = P.p ((w ++ [a]) ++ z) := by simp
      _ ≤ P.p (w ++ [a]) := ih _
      _ ≤ P.p w := P.p_snoc_le w a

/-- Paper Def 2.9. `p ≤ 1`. -/
theorem p_le_one (w : List α) : P.p w ≤ 1 := by
  simpa [P.p_nil] using P.p_append_le [] w

/-- Null histories stay null: `p(w) = 0 ⇒ p(wz) = 0`. -/
theorem p_append_eq_zero {w : List α} (hw : P.p w = 0) (z : List α) : P.p (w ++ z) = 0 :=
  le_antisymm (hw ▸ P.p_append_le w z) (P.p_nonneg _)

/-- Paper Def 2.10. The predictive state `P_w(z) = p(wz)/p(w)`. -/
noncomputable def pred (w : List α) (z : List α) : ℝ := P.p (w ++ z) / P.p w

/-- Paper Def 2.10. Predictive equivalence `h ~_ε h'`: both histories are null, or
both are in the support and have the same predictive state. -/
def EpsEquiv (h h' : List α) : Prop :=
  (P.p h = 0 ∧ P.p h' = 0) ∨
    (P.p h ≠ 0 ∧ P.p h' ≠ 0 ∧ ∀ z, P.p (h ++ z) / P.p h = P.p (h' ++ z) / P.p h')

/-- Paper Lemma 2.11. `~_ε` is an equivalence relation. -/
theorem epsEquiv_equivalence : Equivalence P.EpsEquiv where
  refl h := by
    by_cases h0 : P.p h = 0
    · exact Or.inl ⟨h0, h0⟩
    · exact Or.inr ⟨h0, h0, fun _ => rfl⟩
  symm := by
    rintro h h' (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h2, h1, fun z => (h3 z).symm⟩
  trans := by
    rintro h h' h'' (⟨h1, h2⟩ | ⟨h1, h2, h3⟩) (⟨g1, g2⟩ | ⟨g1, g2, g3⟩)
    · exact Or.inl ⟨h1, g2⟩
    · exact absurd h2 g1
    · exact absurd g1 h2
    · exact Or.inr ⟨h1, g2, fun z => (h3 z).trans (g3 z)⟩

/-- The predictive equivalence as a `Setoid`. -/
def epsSetoid : Setoid (List α) := ⟨P.EpsEquiv, P.epsEquiv_equivalence⟩

/-- Paper Lemma 2.11. `~_ε` is a right congruence. -/
theorem epsEquiv_rightCongr : RightCongr P.EpsEquiv := by
  rintro h h' e (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
  · exact Or.inl ⟨P.p_append_eq_zero h1 _, P.p_append_eq_zero h2 _⟩
  · by_cases he : P.p (h ++ [e]) = 0
    · refine Or.inl ⟨he, ?_⟩
      have := h3 [e]
      rw [he, zero_div, eq_comm, div_eq_zero_iff] at this
      exact this.resolve_right h2
    · have he' : P.p (h' ++ [e]) ≠ 0 := by
        intro he'
        have := h3 [e]
        rw [he', zero_div, div_eq_zero_iff] at this
        exact this.elim he h1
      refine Or.inr ⟨he, he', fun z => ?_⟩
      have hz := h3 ([e] ++ z)
      have he1 := h3 [e]
      calc P.p (h ++ [e] ++ z) / P.p (h ++ [e])
          = (P.p (h ++ ([e] ++ z)) / P.p h) / (P.p (h ++ [e]) / P.p h) := by
            rw [div_div_div_cancel_right₀ h1, List.append_assoc]
        _ = (P.p (h' ++ ([e] ++ z)) / P.p h') / (P.p (h' ++ [e]) / P.p h') := by
            rw [hz, he1]
        _ = P.p (h' ++ [e] ++ z) / P.p (h' ++ [e]) := by
            rw [div_div_div_cancel_right₀ h2, List.append_assoc]

/-- Paper Lemma 2.11. `h ~_ε h' ⇒ hz ~_ε h'z`. -/
theorem epsEquiv_append {h h' : List α} (H : P.EpsEquiv h h') (z : List α) :
    P.EpsEquiv (h ++ z) (h' ++ z) :=
  P.epsEquiv_rightCongr.append H z

/-- Paper Lemma 2.11. `P_h` is a function of `ε(h)` (on the support). -/
theorem pred_eq_of_epsEquiv {h h' : List α} (H : P.EpsEquiv h h') (hh : P.p h ≠ 0) :
    P.pred h = P.pred h' := by
  rcases H with ⟨h1, _⟩ | ⟨_, _, h3⟩
  · exact absurd h1 hh
  · funext z; exact h3 z

/-- Paper Lemma 2.11. The semantics `Φ(w) = P_w` if `w ∈ Supp(p)`, `⊥` otherwise.
-/
noncomputable def Phi (w : List α) : Option (List α → ℝ) :=
  open Classical in if P.p w = 0 then none else some (P.pred w)

theorem epsEquiv_iff_Phi_eq (h h' : List α) : P.EpsEquiv h h' ↔ P.Phi h = P.Phi h' := by
  unfold Phi pred
  by_cases h1 : P.p h = 0 <;> by_cases h2 : P.p h' = 0 <;>
    simp [EpsEquiv, h1, h2, funext_iff]

/-- Paper Lemma 2.11. `~_ε = ~_Φ`. -/
theorem epsEquiv_iff_resEquiv_Phi (h h' : List α) :
    P.EpsEquiv h h' ↔ ResEquiv P.Phi h h' := by
  constructor
  · intro H z
    exact (P.epsEquiv_iff_Phi_eq _ _).mp (P.epsEquiv_append H z)
  · intro H
    exact (P.epsEquiv_iff_Phi_eq _ _).mpr (by simpa using H [])

/-! ### Def 2.11: the joint state `J = (ε, κ)` -/

/-- Paper Def 2.13. Joint equivalence `h ~_J h'` iff `h ~_ε h'` and `h ~_V h'`. -/
def JEquiv (V : List α → Bool) (h h' : List α) : Prop := P.EpsEquiv h h' ∧ ResEquiv V h h'

/-- Paper Def 2.13. `~_J = ~_ε ∩ ~_V = ~_{(Φ,V)}`. -/
theorem jEquiv_iff_resEquiv_pair (V : List α → Bool) (h h' : List α) :
    P.JEquiv V h h' ↔ ResEquiv (fun w => (P.Phi w, V w)) h h' := by
  rw [← jointEquiv_iff_resEquiv_pair, JEquiv, JointEquiv, epsEquiv_iff_resEquiv_Phi]

/-- Paper Def 2.13. `~_J` is a right congruence. -/
theorem jEquiv_rightCongr (V : List α → Bool) : RightCongr (P.JEquiv V) :=
  P.epsEquiv_rightCongr.inf (resEquiv_rightCongr V)

/-- Paper Def 2.13. `~_J` is an equivalence relation. -/
theorem jEquiv_equivalence (V : List α → Bool) : Equivalence (P.JEquiv V) where
  refl h := ⟨P.epsEquiv_equivalence.refl h, ResEquiv.refl V h⟩
  symm H := ⟨P.epsEquiv_equivalence.symm H.1, H.2.symm⟩
  trans H H' := ⟨P.epsEquiv_equivalence.trans H.1 H'.1, H.2.trans H'.2⟩

/-- The joint equivalence as a `Setoid`; `J(h)` is the class of `h`. -/
def jSetoid (V : List α → Bool) : Setoid (List α) := ⟨P.JEquiv V, P.jEquiv_equivalence V⟩

/-- Paper Def 2.13. As setoids, `~_J = ~_ε ⊓ ~_κ`. -/
theorem jSetoid_eq_inf (V : List α → Bool) : P.jSetoid V = P.epsSetoid ⊓ resSetoid V :=
  Setoid.ext fun a b =>
    (Setoid.inf_iff_and (r := P.epsSetoid) (s := resSetoid V) (x := a) (y := b)).symm

/-- Paper Prop 4.2 (index sandwich) for `J = (ε, κ)`:
`max(ind ε, ind κ) ≤ ind J ≤ ind ε · ind κ` when `ind ε, ind κ < ∞`. -/
theorem index_sandwich (V : List α → Bool) [Finite (Quotient P.epsSetoid)]
    [Finite (Quotient (resSetoid V))] :
    max (Nat.card (Quotient P.epsSetoid)) (Nat.card (Quotient (resSetoid V))) ≤
        Nat.card (Quotient (P.jSetoid V)) ∧
      Nat.card (Quotient (P.jSetoid V)) ≤
        Nat.card (Quotient P.epsSetoid) * Nat.card (Quotient (resSetoid V)) := by
  rw [jSetoid_eq_inf]
  exact ⟨max_card_quotient_le_card_inf _ _, card_quotient_inf_le_mul _ _⟩

/-- Paper Prop 4.2: `ind J = ind κ ⇔ ~_κ ⊆ ~_ε`, and `ind J = ind ε ⇔ ~_ε ⊆ ~_κ`. -/
theorem index_eq_iff (V : List α → Bool) [Finite (Quotient P.epsSetoid)]
    [Finite (Quotient (resSetoid V))] :
    (Nat.card (Quotient (P.jSetoid V)) = Nat.card (Quotient (resSetoid V)) ↔
        ∀ h h', ResEquiv V h h' → P.EpsEquiv h h') ∧
      (Nat.card (Quotient (P.jSetoid V)) = Nat.card (Quotient P.epsSetoid) ↔
        ∀ h h', P.EpsEquiv h h' → ResEquiv V h h') := by
  rw [jSetoid_eq_inf]
  exact ⟨card_inf_eq_right_iff _ _, card_inf_eq_left_iff _ _⟩

/-! ### Paper Cor 3.3: three canonical machines -/

/-- Paper Cor 3.3. The κ-machine `P_V`, the predictive machine `P_Φ` and the joint machine
`P_{(Φ,V)}` are reachable exact presentations of their semantics (hence, by Thm 3.2, the unique
minimal ones), and the joint machine's states are exactly the `J`-classes. -/
theorem three_machines (V : List α → Bool) :
    ((canonical V).IsExact V ∧ (canonical V).IsReachable) ∧
      ((canonical P.Phi).IsExact P.Phi ∧ (canonical P.Phi).IsReachable) ∧
      ((canonical fun w => (P.Phi w, V w)).IsExact (fun w => (P.Phi w, V w)) ∧
        (canonical fun w => (P.Phi w, V w)).IsReachable) ∧
      resSetoid (fun w => (P.Phi w, V w)) = P.jSetoid V :=
  ⟨⟨canonical_isExact V, canonical_isReachable V⟩,
    ⟨canonical_isExact _, canonical_isReachable _⟩,
    ⟨canonical_isExact _, canonical_isReachable _⟩,
    Setoid.ext fun h h' => (P.jEquiv_iff_resEquiv_pair V h h').symm⟩

/-- Paper Cor 3.3. The joint machine is the reachable part of the product of the predictive and
κ-machines: `ind J` equals the number of reachable pairs `([w]_ε, [w]_κ)`. -/
theorem index_J_eq_reachable_pairs (V : List α → Bool) :
    Nat.card (Quotient (P.jSetoid V)) =
      Nat.card (Set.range fun w => (Quotient.mk P.epsSetoid w, Quotient.mk (resSetoid V) w)) := by
  let g : List α → Quotient P.epsSetoid × Quotient (resSetoid V) :=
    fun w => (Quotient.mk P.epsSetoid w, Quotient.mk (resSetoid V) w)
  let Φ : Quotient (P.jSetoid V) → Set.range g :=
    Quotient.lift (s := P.jSetoid V) (fun w => ⟨g w, w, rfl⟩) (fun h h' H => by
      apply Subtype.ext
      simp only [g, Prod.mk.injEq]
      exact ⟨Quotient.sound H.1, Quotient.sound H.2⟩)
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro a b hab
      induction a using Quotient.ind
      induction b using Quotient.ind
      have := congrArg Subtype.val hab
      simp only [Φ, g, Quotient.lift_mk, Prod.mk.injEq] at this
      exact Quotient.sound ⟨Quotient.exact this.1, Quotient.exact this.2⟩
    · rintro ⟨_, w, rfl⟩
      exact ⟨Quotient.mk _ w, rfl⟩
  exact Nat.card_eq_of_bijective Φ hΦ

end Process

end LikelyAllowed
