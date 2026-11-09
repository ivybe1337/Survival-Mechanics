/-
Copyright (c) 2026 Joshua Matthew Carter. Released under the MIT-0 license.
Authors: Joshua Matthew Carter
-/
import LikelyAllowed.Nondet
import LikelyAllowed.Predictive
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Paper Theorem 4.1: prediction and admissibility are independent

`Σ = {a, b}` (`a = false`, `b = true`), `V = V_bb`, and `p_{α,β}` emits independent symbols with
`Pr(a) = α` at even positions and `Pr(a) = β` at odd positions, `α ≠ β ∈ (0,1)`.
(Here `α, β` are called `pa, pb`.)
-/

namespace LikelyAllowed

open Finset

section Parity

variable (pa pb : ℝ)

/-- Per-position symbol law of `p_{α,β}`. -/
noncomputable def qpar (t : ℕ) (x : Bool) : ℝ :=
  if x then 1 - (if t % 2 = 0 then pa else pb) else (if t % 2 = 0 then pa else pb)

/-- `p_{α,β}` started at position `t`. -/
noncomputable def ppar : ℕ → List Bool → ℝ
  | _, [] => 1
  | t, x :: w => qpar pa pb t x * ppar (t + 1) w

theorem ppar_append (t : ℕ) (h z : List Bool) :
    ppar pa pb t (h ++ z) = ppar pa pb t h * ppar pa pb (t + h.length) z := by
  induction h generalizing t with
  | nil => simp [ppar]
  | cons x h ih =>
    simp only [List.cons_append, ppar, ih, List.length_cons]
    rw [show t + 1 + h.length = t + (h.length + 1) by omega]
    ring

theorem qpar_parity {t t' : ℕ} (ht : t % 2 = t' % 2) (x : Bool) :
    qpar pa pb t x = qpar pa pb t' x := by
  simp [qpar, ht]

theorem ppar_parity {t t' : ℕ} (ht : t % 2 = t' % 2) (z : List Bool) :
    ppar pa pb t z = ppar pa pb t' z := by
  induction z generalizing t t' with
  | nil => rfl
  | cons x z ih =>
    simp only [ppar, qpar_parity pa pb ht x, ih (show (t + 1) % 2 = (t' + 1) % 2 by omega)]

variable {pa pb}

theorem qpar_pos (ha : 0 < pa ∧ pa < 1) (hb : 0 < pb ∧ pb < 1) (t : ℕ) (x : Bool) :
    0 < qpar pa pb t x := by
  unfold qpar
  split_ifs <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem ppar_pos (ha : 0 < pa ∧ pa < 1) (hb : 0 < pb ∧ pb < 1) (t : ℕ) (z : List Bool) :
    0 < ppar pa pb t z := by
  induction z generalizing t with
  | nil => simp [ppar]
  | cons x z ih => exact mul_pos (qpar_pos ha hb t x) (ih _)

/-- Paper Thm 4.1: the parity process `p_{α,β}`. -/
noncomputable def parityProcess (ha : 0 < pa ∧ pa < 1) (hb : 0 < pb ∧ pb < 1) : Process Bool where
  p := ppar pa pb 0
  p_nil := rfl
  p_nonneg w := (ppar_pos ha hb 0 w).le
  p_sum w := by
    rw [Fintype.sum_bool, ppar_append, ppar_append]
    simp only [ppar, mul_one]
    rw [← mul_add]
    simp [qpar]

variable (ha : 0 < pa ∧ pa < 1) (hb : 0 < pb ∧ pb < 1)

theorem parity_pred (h z : List Bool) :
    (parityProcess ha hb).pred h z = ppar pa pb h.length z := by
  unfold Process.pred
  simp only [parityProcess, ppar_append, zero_add]
  field_simp [(ppar_pos ha hb 0 h).ne']

/-- Paper Thm 4.1(a): `ε(h)` is determined by `|h| mod 2` (and conversely, since `α ≠ β`). -/
theorem parity_epsEquiv_iff (hab : pa ≠ pb) (h h' : List Bool) :
    (parityProcess ha hb).EpsEquiv h h' ↔ h.length % 2 = h'.length % 2 := by
  have hne : ∀ w, (parityProcess ha hb).p w ≠ 0 := fun w => (ppar_pos ha hb 0 w).ne'
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, -, H⟩)
    · exact absurd h1 (hne h)
    · have this : (parityProcess ha hb).pred h [false] = (parityProcess ha hb).pred h' [false] :=
        H [false]
      rw [parity_pred, parity_pred] at this
      simp only [ppar, qpar, Bool.false_eq_true, ↓reduceIte, mul_one] at this
      rcases Nat.mod_two_eq_zero_or_one h.length with e | e <;>
        rcases Nat.mod_two_eq_zero_or_one h'.length with e' | e' <;>
        simp_all
  · intro H
    refine Or.inr ⟨hne h, hne h', fun z => ?_⟩
    change (parityProcess ha hb).pred h z = (parityProcess ha hb).pred h' z
    rw [parity_pred, parity_pred, ppar_parity pa pb H z]

/-- Paper Thm 4.1: `J(h) = J(h')` iff same length parity and same `κ`-state (`A`, `B`, `D`). -/
theorem parity_jEquiv_iff (hab : pa ≠ pb) (h h' : List Bool) :
    (parityProcess ha hb).JEquiv noBB h h' ↔
      h.length % 2 = h'.length % 2 ∧ Dκ.reach h = Dκ.reach h' := by
  rw [Process.JEquiv, parity_epsEquiv_iff ha hb hab, Dκ_reach_eq_iff]

/-- The length parity `|h| mod 2 ∈ Fin 2`. -/
def par (h : List Bool) : Fin 2 := ⟨h.length % 2, Nat.mod_lt _ (by norm_num)⟩

/-- The joint-state invariant `(|h| mod 2, κ(h)) ∈ Fin 2 × Fin 3`. -/
def jInv (h : List Bool) : Fin 2 × Fin 3 := (par h, Dκ.reach h)

theorem jInv_eq_iff (h h' : List Bool) :
    jInv h = jInv h' ↔ h.length % 2 = h'.length % 2 ∧ Dκ.reach h = Dκ.reach h' := by
  simp [jInv, par, Fin.ext_iff]

/-- The six representatives `Λ, a, b, ab, bb, abb` of Paper Thm 4.1(c). -/
def sixReps : Fin 6 → List Bool :=
  ![[], [false], [true], [false, true], [true, true], [false, true, true]]

theorem jInv_sixReps_bijective : Function.Bijective (fun i => jInv (sixReps i)) := by
  decide

/-- Paper Thm 4.1(c): the six representatives are pairwise not `J`-equivalent. -/
theorem sixReps_pairwise_not_jEquiv (hab : pa ≠ pb) {i j : Fin 6} (hij : i ≠ j) :
    ¬ (parityProcess ha hb).JEquiv noBB (sixReps i) (sixReps j) := by
  rw [parity_jEquiv_iff ha hb hab, ← jInv_eq_iff]
  exact fun H => hij (jInv_sixReps_bijective.1 H)

/-- Paper Thm 4.1(c): `J` has exactly six classes. -/
theorem parity_index_J (hab : pa ≠ pb) :
    Nat.card (Quotient ((parityProcess ha hb).jSetoid noBB)) = 6 := by
  let Φ : Quotient ((parityProcess ha hb).jSetoid noBB) → Fin 2 × Fin 3 :=
    Quotient.lift (s := (parityProcess ha hb).jSetoid noBB) jInv
      (fun h h' H => (jInv_eq_iff h h').mpr ((parity_jEquiv_iff ha hb hab h h').mp H))
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro x y hxy
      induction x using Quotient.ind
      induction y using Quotient.ind
      exact Quotient.sound ((parity_jEquiv_iff ha hb hab _ _).mpr ((jInv_eq_iff _ _).mp hxy))
    · intro v
      obtain ⟨i, hi⟩ := jInv_sixReps_bijective.2 v
      exact ⟨Quotient.mk _ (sixReps i), hi⟩
  rw [Nat.card_eq_of_bijective Φ hΦ]
  simp

/-- Paper Thm 4.1(a): `ε` has exactly two classes. -/
theorem parity_index_eps (hab : pa ≠ pb) :
    Nat.card (Quotient (parityProcess ha hb).epsSetoid) = 2 := by
  let Φ : Quotient (parityProcess ha hb).epsSetoid → Fin 2 :=
    Quotient.lift (s := (parityProcess ha hb).epsSetoid) par
      (fun h h' H => Fin.ext ((parity_epsEquiv_iff ha hb hab h h').mp H))
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro x y hxy
      induction x using Quotient.ind
      induction y using Quotient.ind
      refine Quotient.sound ((parity_epsEquiv_iff ha hb hab _ _).mpr ?_)
      exact Fin.ext_iff.mp hxy
    · intro v
      refine ⟨Quotient.mk _ (List.replicate v.val false), ?_⟩
      exact Fin.ext (by simp [Φ, par, Nat.mod_eq_of_lt v.isLt])
  rw [Nat.card_eq_of_bijective Φ hΦ]
  simp

/-- Paper Thm 4.1(d): `Λ ~_κ a` but `Λ ≁_ε a`, while `a ~_ε b` but `a ≁_κ b`; neither
partition refines the other. -/
theorem parity_incomparable (hab : pa ≠ pb) :
    ResEquiv noBB [] [false] ∧ ¬ (parityProcess ha hb).EpsEquiv [] [false] ∧
      (parityProcess ha hb).EpsEquiv [false] [true] ∧ ¬ ResEquiv noBB [false] [true] := by
  refine ⟨(Dκ_reach_eq_iff _ _).mp (by decide), ?_, ?_, ?_⟩
  · rw [parity_epsEquiv_iff ha hb hab]; decide
  · rw [parity_epsEquiv_iff ha hb hab]; rfl
  · rw [← Dκ_reach_eq_iff]; decide

end Parity

end LikelyAllowed
