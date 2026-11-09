/-
Copyright (c) 2026 Joshua Matthew Carter. Released under the MIT-0 license.
Authors: Joshua Matthew Carter
-/
import LikelyAllowed.Canonical
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.VecNotation

/-!
# §8 Beyond determinism: universal presentations (Paper Def 8.1, Obs 8.2,
Lemmas 8.3 and 8.4, Prop 8.5) -/

namespace LikelyAllowed

open Finset

universe u v w

/-- Paper Def 8.1. A universal presentation `Q = (S, s₀, δ : S × Σ → 2^S ∖ {∅}, ℓ : S → {0,1})`. -/
structure UPres (α : Type u) (S : Type v) where
  /-- start state `s₀` -/
  start : S
  /-- nondeterministic transition `δ` -/
  δ : S → α → Finset S
  δ_nonempty : ∀ s a, (δ s a).Nonempty
  /-- state labels `ℓ` -/
  ℓ : S → Bool

namespace UPres

variable {α : Type u} {S : Type v} [DecidableEq S] (Q : UPres α S)

/-- `δ(M, a) = ⋃_{s ∈ M} δ(s, a)`. -/
def img (M : Finset S) (a : α) : Finset S := M.biUnion fun s => Q.δ s a

/-- `δ*(M, w)`. -/
def runSet (M : Finset S) (w : List α) : Finset S := w.foldl Q.img M

/-- Paper §8. `Reach(Λ) = {s₀}`, `Reach(he) = δ(Reach(h), e)`. -/
def Reach (w : List α) : Finset S := Q.runSet {Q.start} w

/-- Paper §8. `safe(M) = ⋀_{s ∈ M} ℓ(s)`. -/
def safe (M : Finset S) : Prop := ∀ s ∈ M, Q.ℓ s = true

instance (M : Finset S) : Decidable (Q.safe M) := by unfold safe; infer_instance

/-- Paper §8. `Q` is exact for `V`: `safe(Reach(h)) = V(h)` for all `h`. -/
def IsExact (V : List α → Bool) : Prop := ∀ h, Q.safe (Q.Reach h) ↔ V h = true

@[simp] theorem runSet_nil (M : Finset S) : Q.runSet M [] = M := rfl

@[simp] theorem runSet_cons (M : Finset S) (a : α) (w : List α) :
    Q.runSet M (a :: w) = Q.runSet (Q.img M a) w := rfl

theorem runSet_append (M : Finset S) (w z : List α) :
    Q.runSet M (w ++ z) = Q.runSet (Q.runSet M w) z := List.foldl_append

theorem Reach_append (w z : List α) : Q.Reach (w ++ z) = Q.runSet (Q.Reach w) z :=
  Q.runSet_append _ _ _

theorem Reach_snoc (w : List α) (a : α) : Q.Reach (w ++ [a]) = Q.img (Q.Reach w) a := by
  rw [Reach_append]; rfl

theorem img_union (M N : Finset S) (a : α) : Q.img (M ∪ N) a = Q.img M a ∪ Q.img N a :=
  union_biUnion

theorem img_mono {M N : Finset S} (h : M ⊆ N) (a : α) : Q.img M a ⊆ Q.img N a :=
  biUnion_subset_biUnion_of_subset_left _ h

theorem img_empty (a : α) : Q.img ∅ a = ∅ := rfl

theorem runSet_union (M N : Finset S) (w : List α) :
    Q.runSet (M ∪ N) w = Q.runSet M w ∪ Q.runSet N w := by
  induction w generalizing M N with
  | nil => rfl
  | cons a w ih => simp only [runSet_cons, img_union, ih]

theorem runSet_mono {M N : Finset S} (h : M ⊆ N) (w : List α) :
    Q.runSet M w ⊆ Q.runSet N w := by
  induction w generalizing M N with
  | nil => exact h
  | cons a w ih => exact ih (Q.img_mono h a)

theorem runSet_empty (w : List α) : Q.runSet ∅ w = ∅ := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa [runSet_cons, img_empty] using ih

theorem Reach_nonempty (w : List α) : (Q.Reach w).Nonempty := by
  induction w using List.reverseRecOn with
  | nil => exact singleton_nonempty _
  | append_singleton w a ih =>
    rw [Reach_snoc]
    obtain ⟨s, hs⟩ := ih
    obtain ⟨t, ht⟩ := Q.δ_nonempty s a
    exact ⟨t, mem_biUnion.mpr ⟨s, hs, ht⟩⟩

/-- `δ*(M, w) = ⋃_{s ∈ M} δ*({s}, w)` (membership form). -/
theorem mem_runSet_iff {M : Finset S} {w : List α} {t : S} :
    t ∈ Q.runSet M w ↔ ∃ s ∈ M, t ∈ Q.runSet {s} w := by
  induction M using Finset.induction_on with
  | empty => simp [runSet_empty]
  | insert s M _ ih =>
    rw [insert_eq, runSet_union, mem_union, ih]
    simp

theorem safe_union (M N : Finset S) : Q.safe (M ∪ N) ↔ Q.safe M ∧ Q.safe N := by
  simp only [safe, mem_union]
  exact ⟨fun h => ⟨fun s hs => h s (Or.inl hs), fun s hs => h s (Or.inr hs)⟩,
    fun h s hs => hs.elim (h.1 s) (h.2 s)⟩

omit [DecidableEq S] in
theorem safe_mono {M N : Finset S} (h : M ⊆ N) (hN : Q.safe N) : Q.safe M :=
  fun s hs => hN s (h hs)

omit [DecidableEq S] in
@[simp] theorem safe_singleton (s : S) : Q.safe {s} ↔ Q.ℓ s = true := by simp [safe]

/-- Paper Obs 8.2. `Q` is exact iff the NFA `(S, s₀, δ, F = ℓ⁻¹(0))` accepts exactly
the death language `V⁻¹(0)`: some reachable state after reading `h` has label `0` iff `V(h) = 0`. -/
theorem isExact_iff_accepts {V : List α → Bool} :
    Q.IsExact V ↔ ∀ h, (∃ s ∈ Q.Reach h, Q.ℓ s = false) ↔ V h = false := by
  refine forall_congr' fun h => ?_
  cases hv : V h <;> simp [safe]

/-- Paper Lemma 8.3. For an exact universal presentation, `Reach(h) = Reach(h') ⇒
h ~_V h'`: masks refine `κ`. -/
theorem IsExact.resEquiv_of_Reach_eq {V : List α → Bool} {Q : UPres α S} (hQ : Q.IsExact V)
    {h h' : List α} (hh : Q.Reach h = Q.Reach h') : ResEquiv V h h' := by
  intro z
  rw [Bool.eq_iff_iff, ← hQ, ← hQ, Reach_append, Reach_append, hh]

/-- Paper Lemma 8.3 (subset bound). `ind κ ≤ 2^{|S|} - 1`. -/
theorem IsExact.card_quotient_le [Fintype S] {V : List α → Bool} {Q : UPres α S}
    (hQ : Q.IsExact V) : Nat.card (Quotient (resSetoid V)) ≤ 2 ^ Fintype.card S - 1 := by
  classical
  -- the class map factors through `Reach`, whose values are nonempty subsets of `S`
  let T := {M : Finset S // M.Nonempty}
  let g : T → Quotient (resSetoid V) := fun M =>
    if hM : ∃ h, Q.Reach h = M.1 then Quotient.mk _ hM.choose else Quotient.mk _ []
  have hg : Function.Surjective g := by
    intro q
    induction q using Quotient.ind with
    | _ h =>
      refine ⟨⟨Q.Reach h, Q.Reach_nonempty h⟩, ?_⟩
      have hex : ∃ h', Q.Reach h' = Q.Reach h := ⟨h, rfl⟩
      simp only [g, hex, ↓reduceDIte]
      exact Quotient.sound (hQ.resEquiv_of_Reach_eq hex.choose_spec)
  have hT : Nat.card T = 2 ^ Fintype.card S - 1 := by
    rw [Nat.card_eq_fintype_card]
    have : Fintype.card T = Fintype.card (Finset S) - 1 := by
      simp only [T, Finset.nonempty_iff_ne_empty]
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    rw [this, Fintype.card_finset]
  exact hT ▸ Nat.card_le_card_of_surjective g hg

/-- Paper Lemma 8.4 (fooling set). If `(x_i, y_i)_{i<k}` satisfy `V(x_i y_i) = 0`
and, for `i ≠ j`, `V(x_i y_j) = 1` or `V(x_j y_i) = 1`, then every exact universal presentation has
at least `k` states. -/
theorem IsExact.card_ge_of_fooling [Fintype S] {V : List α → Bool} {Q : UPres α S}
    (hQ : Q.IsExact V) {k : ℕ} (x y : Fin k → List α)
    (hdiag : ∀ i, V (x i ++ y i) = false)
    (hoff : ∀ i j, i ≠ j → V (x i ++ y j) = true ∨ V (x j ++ y i) = true) :
    k ≤ Fintype.card S := by
  -- pick `s_i ∈ Reach(x_i)` from which `y_i` can reach a state with `ℓ = 0`
  have hpick : ∀ i, ∃ s, s ∈ Q.Reach (x i) ∧ ¬ Q.safe (Q.runSet {s} (y i)) := by
    intro i
    have hns : ¬ Q.safe (Q.Reach (x i ++ y i)) := by
      rw [hQ, hdiag i]; simp
    simp only [safe, not_forall] at hns
    obtain ⟨t, ht, hℓ⟩ := hns
    rw [Reach_append, mem_runSet_iff] at ht
    obtain ⟨s, hs, hts⟩ := ht
    exact ⟨s, hs, fun h => hℓ (h t hts)⟩
  choose f hf using hpick
  -- if `s_i = s_j` with `i ≠ j` then `V(x_j y_i) = V(x_i y_j) = 0`
  have hbad : ∀ i j, f i = f j → V (x j ++ y i) ≠ true := by
    intro i j hij hV
    rw [← hQ, Reach_append] at hV
    have hsub : Q.runSet {f i} (y i) ⊆ Q.runSet (Q.Reach (x j)) (y i) :=
      Q.runSet_mono (by rw [hij]; exact singleton_subset_iff.mpr (hf j).1) _
    exact (hf i).2 (Q.safe_mono hsub hV)
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    rcases hoff i j hne with h | h
    · exact hbad j i hij.symm h
    · exact hbad i j hij h
  simpa using Fintype.card_le_of_injective f hinj

/-- Paper Prop 8.5. An isomorphism of universal presentations: a bijection of states
fixing the start state, commuting with `δ` (as sets) and preserving `ℓ`. -/
def Iso {S' : Type w} [DecidableEq S'] (Q : UPres α S) (Q' : UPres α S') : Prop :=
  ∃ ψ : S ≃ S', ψ Q.start = Q'.start ∧ (∀ s e, (Q.δ s e).image ψ = Q'.δ (ψ s) e) ∧
    ∀ s, Q'.ℓ (ψ s) = Q.ℓ s

end UPres

/-! ### The `bb`-avoidance example (Paper Prop 8.5); `a = false`, `b = true` -/

/-- Paper §4/§8. `V_bb(w) = 1` iff `w` has no two consecutive `b`s. -/
def noBB : List Bool → Bool
  | true :: true :: _ => false
  | _ :: t => noBB t
  | [] => true

/-- `noBB` is the indicator of "no factor `bb`". -/
theorem noBB_iff (w : List Bool) : noBB w = true ↔ ¬ [true, true] <:+: w := by
  induction w with
  | nil => simp [noBB]
  | cons a w ih =>
    rw [List.infix_cons_iff]
    cases a with
    | false => simp [noBB, ih]
    | true =>
      cases w with
      | nil => simp [noBB]
      | cons b w =>
        cases b with
        | true => simp [noBB]
        | false =>
          have : noBB (true :: false :: w) = noBB (false :: w) := rfl
          rw [this, ih]
          simp

theorem noBB_of_cons {a : Bool} {w : List Bool} (h : noBB (a :: w) = true) : noBB w = true := by
  cases a with
  | false => exact h
  | true =>
    cases w with
    | nil => rfl
    | cons b w =>
      cases b with
      | true => exact absurd h (by simp [noBB])
      | false => exact h

/-- The fooling set `(Λ, bb), (b, b), (bb, Λ)` of Paper Prop 8.5. -/
def foolX : Fin 3 → List Bool := ![[], [true], [true, true]]
def foolY : Fin 3 → List Bool := ![[true, true], [true], []]

theorem fool_diag : ∀ i, noBB (foolX i ++ foolY i) = false := by decide

theorem fool_off : ∀ i j, i ≠ j →
    noBB (foolX i ++ foolY j) = true ∨ noBB (foolX j ++ foolY i) = true := by decide

/-- Paper Prop 8.5, lower bound: every exact universal presentation of `V_bb` has `≥
3` states. -/
theorem noBB_card_ge_three {S : Type v} [Fintype S] [DecidableEq S] (Q : UPres Bool S)
    (hQ : Q.IsExact noBB) : 3 ≤ Fintype.card S :=
  hQ.card_ge_of_fooling foolX foolY fool_diag fool_off

/-- Paper Prop 8.5: the transition table of `Q_κ`. -/
def δκ : Fin 3 → Bool → Finset (Fin 3) :=
  ![fun e => if e then {1} else {0}, fun e => if e then {2} else {0}, fun _ => {2}]

/-- Paper Prop 8.5: the transition table of `Q_alt` (same as `Q_κ` except `δ(0,b) =
{0,1}`). -/
def δalt : Fin 3 → Bool → Finset (Fin 3) :=
  ![fun e => if e then {0, 1} else {0}, fun e => if e then {2} else {0}, fun _ => {2}]

/-- The labelling `ℓ = (1, 1, 0)`. -/
def ℓbb : Fin 3 → Bool := ![true, true, false]

/-- Paper Prop 8.5: `Q_κ`. -/
def Qκ : UPres Bool (Fin 3) := ⟨0, δκ, by decide, ℓbb⟩

/-- Paper Prop 8.5: `Q_alt`. -/
def Qalt : UPres Bool (Fin 3) := ⟨0, δalt, by decide, ℓbb⟩

theorem Qκ_inv (w : List Bool) :
    (Qκ.safe (Qκ.runSet {0} w) ↔ noBB w = true) ∧
      (Qκ.safe (Qκ.runSet {1} w) ↔ noBB (true :: w) = true) ∧
        ¬ Qκ.safe (Qκ.runSet {2} w) := by
  induction w with
  | nil => decide
  | cons e w ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    cases e with
    | false =>
      have i0 : Qκ.img {0} false = {0} := by decide
      have i1 : Qκ.img {1} false = {0} := by decide
      have i2 : Qκ.img {2} false = {2} := by decide
      simp only [UPres.runSet_cons, i0, i1, i2]
      exact ⟨h0, h0, h2⟩
    | true =>
      have i0 : Qκ.img {0} true = {1} := by decide
      have i1 : Qκ.img {1} true = {2} := by decide
      have i2 : Qκ.img {2} true = {2} := by decide
      simp only [UPres.runSet_cons, i0, i1, i2]
      exact ⟨h1, by simpa [noBB] using h2, h2⟩

/-- Paper Prop 8.5: `Q_κ` is exact for `V_bb` (for all words). -/
theorem Qκ_exact : Qκ.IsExact noBB := fun w => (Qκ_inv w).1

theorem Qalt_inv (w : List Bool) :
    (Qalt.safe (Qalt.runSet {0} w) ↔ noBB w = true) ∧
      (Qalt.safe (Qalt.runSet {1} w) ↔ noBB (true :: w) = true) ∧
        ¬ Qalt.safe (Qalt.runSet {2} w) := by
  induction w with
  | nil => decide
  | cons e w ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    cases e with
    | false =>
      have i0 : Qalt.img {0} false = {0} := by decide
      have i1 : Qalt.img {1} false = {0} := by decide
      have i2 : Qalt.img {2} false = {2} := by decide
      simp only [UPres.runSet_cons, i0, i1, i2]
      exact ⟨h0, h0, h2⟩
    | true =>
      have i0 : Qalt.img {0} true = {0} ∪ {1} := by decide
      have i1 : Qalt.img {1} true = {2} := by decide
      have i2 : Qalt.img {2} true = {2} := by decide
      simp only [UPres.runSet_cons, i0, i1, i2, UPres.runSet_union, UPres.safe_union]
      refine ⟨?_, by simpa [noBB] using h2, h2⟩
      rw [h0, h1]
      exact ⟨fun h => h.2, fun h => ⟨noBB_of_cons h, h⟩⟩

/-- Paper Prop 8.5: `Q_alt` is exact for `V_bb` (for all words). -/
theorem Qalt_exact : Qalt.IsExact noBB := fun w => (Qalt_inv w).1

/-- Paper Prop 8.5: `Q_κ ≇ Q_alt`. -/
theorem Qκ_not_iso_Qalt : ¬ Qκ.Iso Qalt := by
  rintro ⟨ψ, h0, hδ, -⟩
  have h := hδ 0 true
  have hs : (0 : Fin 3) = Qκ.start := rfl
  rw [hs, h0] at h
  have hl : Qκ.δ Qκ.start true = {1} := rfl
  have hr : Qalt.δ Qalt.start true = {0, 1} := rfl
  rw [hl, hr, image_singleton] at h
  have := congrArg Finset.card h
  simp at this

/-- Paper Prop 8.5: the minimum size of an exact universal presentation of `V_bb` is
`3`. -/
theorem noBB_min_universal_size :
    (∃ Q : UPres Bool (Fin 3), Q.IsExact noBB) ∧
      ∀ (S : Type v) [Fintype S] [DecidableEq S] (Q : UPres Bool S),
        Q.IsExact noBB → 3 ≤ Fintype.card S :=
  ⟨⟨Qκ, Qκ_exact⟩, fun _ _ _ Q hQ => noBB_card_ge_three Q hQ⟩

/-! ### `ind κ = 3` for `V_bb` via the canonical presentation -/

/-- The deterministic automaton underlying `Q_κ`. -/
def Dκ : DetPres Bool Bool (Fin 3) where
  start := 0
  step := ![fun e => if e then 1 else 0, fun e => if e then 2 else 0, fun _ => 2]
  out := ℓbb

theorem Qκ_runSet_singleton (s : Fin 3) (w : List Bool) :
    Qκ.runSet {s} w = {Dκ.run s w} := by
  induction w generalizing s with
  | nil => rfl
  | cons e w ih =>
    have himg : ∀ (s : Fin 3) (e : Bool), Qκ.img {s} e = {Dκ.step s e} := by decide
    rw [UPres.runSet_cons, himg, ih]; rfl

theorem Dκ_exact : Dκ.IsExact noBB := by
  intro w
  have h := Qκ_exact w
  rw [UPres.Reach, Qκ_runSet_singleton, UPres.safe_singleton] at h
  exact Bool.eq_iff_iff.mpr h

theorem Dκ_reachable : Dκ.IsReachable := by
  intro s
  have h : ∀ s : Fin 3, s = Dκ.reach [] ∨ s = Dκ.reach [true] ∨ s = Dκ.reach [true, true] := by
    decide
  rcases h s with h | h | h <;> exact ⟨_, h.symm⟩

/-- The residual state of `V_bb` is the state of `Q_κ`: `h ~_V h'` iff `Dκ` reaches the same
state (`0 = A`: alive, not ending in `b`; `1 = B`: alive, ending in `b`; `2 = D`: dead). -/
theorem Dκ_reach_eq_iff (w w' : List Bool) : Dκ.reach w = Dκ.reach w' ↔ ResEquiv noBB w w' := by
  have hdist : ∀ s s' : Fin 3, s ≠ s' →
      Dκ.out (Dκ.run s []) ≠ Dκ.out (Dκ.run s' []) ∨
        Dκ.out (Dκ.run s [true]) ≠ Dκ.out (Dκ.run s' [true]) := by decide
  refine ⟨Dκ_exact.resEquiv_of_reach_eq, fun H => ?_⟩
  by_contra hne
  have hz : ∀ z, Dκ.out (Dκ.run (Dκ.reach w) z) = Dκ.out (Dκ.run (Dκ.reach w') z) := by
    intro z
    rw [← DetPres.reach_append, ← DetPres.reach_append, Dκ_exact, Dκ_exact]
    exact H z
  rcases hdist _ _ hne with h | h
  · exact h (hz [])
  · exact h (hz [true])

/-- Paper Prop 8.5: `ind κ = 3` for `V_bb`. -/
theorem noBB_index : Nat.card (Quotient (resSetoid noBB)) = 3 := by
  have hbij := ((toCanonical Dκ_reachable Dκ_exact).bijective_iff_kernel Dκ_reachable
    Dκ_exact).mpr Dκ_reach_eq_iff
  rw [← ((toCanonical Dκ_reachable Dκ_exact).bijective_iff_card).mp hbij]
  simp

end LikelyAllowed
