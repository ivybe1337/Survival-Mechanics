/-
Copyright (c) 2026 Joshua Matthew Carter. Released under the MIT-0 license.
Authors: Joshua Matthew Carter
-/
import LikelyAllowed.Residual
import Mathlib.SetTheory.Cardinal.Finite

/-!
# §3 Canonical presentations (Paper Thm 3.2, any codomain)
-/

namespace LikelyAllowed

universe u v w w' w''

variable {α : Type u} {X : Type v}

/-- Paper Def 3.1. A deterministic presentation `P = (S, s₀, δ, ℓ)` with state type `S`,
start state `s₀`, transition `δ : S → α → S` and output `ℓ : S → X`. -/
structure DetPres (α : Type u) (X : Type v) (S : Type w) where
  /-- start state `s₀` -/
  start : S
  /-- transition `δ` -/
  step : S → α → S
  /-- output `ℓ` -/
  out : S → X

namespace DetPres

variable {S : Type w} {S' : Type w'} {S'' : Type w''}

/-- The extended transition `δ*(s, w)`. -/
def run (P : DetPres α X S) (s : S) (w : List α) : S := w.foldl P.step s

/-- The reach map `w ↦ δ*(s₀, w)`. -/
def reach (P : DetPres α X S) (w : List α) : S := P.run P.start w

variable (P : DetPres α X S)

@[simp] theorem run_nil (s : S) : P.run s [] = s := rfl

@[simp] theorem run_cons (s : S) (a : α) (w : List α) :
    P.run s (a :: w) = P.run (P.step s a) w := rfl

theorem run_append (s : S) (w z : List α) : P.run s (w ++ z) = P.run (P.run s w) z :=
  List.foldl_append

@[simp] theorem reach_nil : P.reach [] = P.start := rfl

theorem reach_append (w z : List α) : P.reach (w ++ z) = P.run (P.reach w) z :=
  P.run_append _ _ _

theorem reach_snoc (w : List α) (a : α) : P.reach (w ++ [a]) = P.step (P.reach w) a := by
  rw [reach_append]; rfl

/-- Paper Def 3.1. `P` presents `F` (is exact for `F`): `ℓ(δ*(s₀, w)) = F(w)` for all `w`. -/
def IsExact (F : List α → X) : Prop := ∀ w, P.out (P.reach w) = F w

/-- Paper Def 3.1. `P` is reachable: every state is `δ*(s₀, w)` for some `w`. -/
abbrev IsReachable : Prop := Function.Surjective P.reach

/-- In an exact presentation, the kernel of the reach map is contained in `~_F`. -/
theorem IsExact.resEquiv_of_reach_eq {F : List α → X} {P : DetPres α X S} (hE : P.IsExact F)
    {w w' : List α} (hw : P.reach w = P.reach w') : ResEquiv F w w' := by
  intro z
  rw [← hE, ← hE, reach_append, reach_append, hw]

/-- Paper Def 3.1. A morphism `ψ : P → P'` of deterministic presentations. -/
structure Hom (P : DetPres α X S) (P' : DetPres α X S') where
  /-- the underlying map of states -/
  toFun : S → S'
  map_start : toFun P.start = P'.start
  map_step : ∀ s a, toFun (P.step s a) = P'.step (toFun s) a
  map_out : ∀ s, P'.out (toFun s) = P.out s

namespace Hom

variable {P} {P' : DetPres α X S'} {P'' : DetPres α X S''}

theorem ext' {f g : Hom P P'} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

theorem map_run (f : Hom P P') (s : S) (w : List α) :
    f.toFun (P.run s w) = P'.run (f.toFun s) w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => simp [ih, f.map_step]

theorem map_reach (f : Hom P P') (w : List α) : f.toFun (P.reach w) = P'.reach w := by
  rw [reach, map_run, f.map_start]; rfl

/-- Morphisms out of a reachable presentation are unique. -/
theorem eq_of_reachable (hR : P.IsReachable) (f g : Hom P P') : f = g := by
  apply ext'
  funext s
  obtain ⟨w, rfl⟩ := hR s
  rw [map_reach, map_reach]

/-- Identity morphism. -/
def id (P : DetPres α X S) : Hom P P := ⟨fun s => s, rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- Composition of morphisms. -/
def comp (g : Hom P' P'') (f : Hom P P') : Hom P P'' where
  toFun := g.toFun ∘ f.toFun
  map_start := by simp [f.map_start, g.map_start]
  map_step s a := by simp [f.map_step, g.map_step]
  map_out s := by simp [f.map_out, g.map_out]

/-- Paper Thm 3.2. The inverse of a bijective morphism is a morphism. -/
noncomputable def inv (f : Hom P P') (hf : Function.Bijective f.toFun) : Hom P' P :=
  have hinv : ∀ s', f.toFun ((Equiv.ofBijective _ hf).symm s') = s' := fun s' =>
    (Equiv.ofBijective _ hf).apply_symm_apply s'
  { toFun := (Equiv.ofBijective _ hf).symm
    map_start := by
      apply hf.1
      rw [hinv, f.map_start]
    map_step := by
      intro s a
      apply hf.1
      rw [hinv, f.map_step, hinv]
    map_out := by
      intro s
      rw [← f.map_out, hinv] }

theorem inv_left (f : Hom P P') (hf : Function.Bijective f.toFun) (s : S) :
    (f.inv hf).toFun (f.toFun s) = s :=
  (Equiv.ofBijective _ hf).symm_apply_apply s

theorem inv_right (f : Hom P P') (hf : Function.Bijective f.toFun) (s' : S') :
    f.toFun ((f.inv hf).toFun s') = s' :=
  (Equiv.ofBijective _ hf).apply_symm_apply s'

end Hom

end DetPres

open DetPres

/-! ### The canonical presentation `P_F` -/

/-- Paper Thm 3.2. The canonical presentation
`P_F = (Σ*/~_F, [Λ], [h]·a = [ha], ℓ([h]) = F(h))`. -/
def canonical (F : List α → X) : DetPres α X (Quotient (resSetoid F)) where
  start := Quotient.mk _ []
  step q a := Quotient.lift (s := resSetoid F) (fun h => Quotient.mk (resSetoid F) (h ++ [a]))
    (fun h h' H => Quotient.sound (resEquiv_snoc (show ResEquiv F h h' from H) a)) q
  out := Quotient.lift (s := resSetoid F) F (fun _ _ H => ResEquiv.apply_eq H)

section Canonical
variable (F : List α → X)

@[simp] theorem canonical_step_mk (h : List α) (a : α) :
    (canonical F).step (Quotient.mk _ h) a = Quotient.mk _ (h ++ [a]) := rfl

@[simp] theorem canonical_out_mk (h : List α) :
    (canonical F).out (Quotient.mk _ h) = F h := rfl

theorem canonical_run_mk (h w : List α) :
    (canonical F).run (Quotient.mk _ h) w = Quotient.mk _ (h ++ w) := by
  induction w generalizing h with
  | nil => simp
  | cons a w ih => rw [run_cons, canonical_step_mk, ih]; simp

theorem canonical_reach (w : List α) :
    (canonical F).reach w = Quotient.mk (resSetoid F) w := by
  change (canonical F).run (Quotient.mk _ []) w = _
  simpa using canonical_run_mk F [] w

/-- Paper Thm 3.2(a). `P_F` presents `F`. -/
theorem canonical_isExact : (canonical F).IsExact F := by
  intro w; rw [canonical_reach]; rfl

/-- Paper Thm 3.2(a). `P_F` is reachable. -/
theorem canonical_isReachable : (canonical F).IsReachable := by
  intro q
  induction q using Quotient.ind with
  | _ w => exact ⟨w, canonical_reach F w⟩

variable {F} {S : Type w} {P : DetPres α X S}

/-- Paper Thm 3.2(b). The morphism from a reachable exact presentation to `P_F`:
`δ*(s₀, w) ↦ [w]_F`. -/
noncomputable def toCanonical (hR : P.IsReachable) (hE : P.IsExact F) : Hom P (canonical F) :=
  have key : ∀ w, Quotient.mk (resSetoid F) (Function.surjInv hR (P.reach w)) =
      Quotient.mk (resSetoid F) w := fun w =>
    Quotient.sound (hE.resEquiv_of_reach_eq (Function.surjInv_eq hR (P.reach w)))
  { toFun := fun s => Quotient.mk (resSetoid F) (Function.surjInv hR s)
    map_start := key []
    map_step := by
      intro s a
      obtain ⟨w, rfl⟩ := hR s
      rw [← reach_snoc, key, key]; rfl
    map_out := by
      intro s
      obtain ⟨w, rfl⟩ := hR s
      rw [key, canonical_out_mk, hE] }

/-- Every morphism into `P_F` sends `δ*(s₀,w)` to `[w]_F`. -/
theorem DetPres.Hom.toCanonical_reach (f : Hom P (canonical F)) (w : List α) :
    f.toFun (P.reach w) = Quotient.mk (resSetoid F) w := by
  rw [f.map_reach, canonical_reach]

/-- Paper Thm 3.2(b) (existence and uniqueness). Every reachable exact
presentation has exactly one morphism to `P_F`. -/
theorem existsUnique_hom_canonical (hR : P.IsReachable) (hE : P.IsExact F) :
    ∃ f : Hom P (canonical F), ∀ g : Hom P (canonical F), g = f :=
  ⟨toCanonical hR hE, fun g => Hom.eq_of_reachable hR g _⟩

/-- Paper Thm 3.2(b) (surjectivity). Any morphism into `P_F` is surjective. -/
theorem DetPres.Hom.surjective_toCanonical (f : Hom P (canonical F)) :
    Function.Surjective f.toFun := by
  intro q
  induction q using Quotient.ind with
  | _ w => exact ⟨P.reach w, f.toCanonical_reach w⟩

/-- Paper Thm 3.2(c). For a reachable exact presentation, the (unique) morphism
to `P_F` is bijective iff the kernel of the reach map is exactly `~_F`. -/
theorem DetPres.Hom.bijective_iff_kernel (hR : P.IsReachable) (hE : P.IsExact F)
    (f : Hom P (canonical F)) :
    Function.Bijective f.toFun ↔ ∀ w w', P.reach w = P.reach w' ↔ ResEquiv F w w' := by
  constructor
  · intro hf w w'
    refine ⟨hE.resEquiv_of_reach_eq, fun H => hf.1 ?_⟩
    rw [f.toCanonical_reach, f.toCanonical_reach]
    exact Quotient.sound H
  · intro H
    refine ⟨?_, f.surjective_toCanonical⟩
    intro s s' hss
    obtain ⟨w, rfl⟩ := hR s
    obtain ⟨w', rfl⟩ := hR s'
    rw [f.toCanonical_reach, f.toCanonical_reach] at hss
    exact (H w w').mpr (Quotient.exact hss)

/-- Paper Thm 3.2(d). For a reachable exact presentation
with finitely many states, the morphism to `P_F` is bijective iff `|S| = ind(~_F)`. -/
theorem DetPres.Hom.bijective_iff_card [Finite S] (f : Hom P (canonical F)) :
    Function.Bijective f.toFun ↔ Nat.card S = Nat.card (Quotient (resSetoid F)) := by
  rw [Nat.bijective_iff_surjective_and_card]
  exact ⟨fun h => h.2, fun h => ⟨f.surjective_toCanonical, h⟩⟩

/-- Paper Thm 3.2(c) (isomorphism). If the morphism `P → P_F` is bijective, then
`P ≅ P_F`: there are morphisms both ways, mutually inverse, and they are the unique such morphisms.
-/
theorem iso_canonical_of_bijective (hR : P.IsReachable) (f : Hom P (canonical F))
    (hf : Function.Bijective f.toFun) :
    ∃ g : Hom (canonical F) P,
      (∀ s, g.toFun (f.toFun s) = s) ∧ (∀ q, f.toFun (g.toFun q) = q) ∧
      (∀ f' : Hom P (canonical F), f' = f) ∧ (∀ g' : Hom (canonical F) P, g' = g) :=
  ⟨f.inv hf, f.inv_left hf, f.inv_right hf, fun f' => Hom.eq_of_reachable hR f' f,
    fun g' => Hom.eq_of_reachable (canonical_isReachable F) g' _⟩

/-- Paper Thm 3.2(d). Minimality: every reachable exact presentation has at least `ind(~_F)`
states. -/
theorem card_canonical_le [Finite S] (hR : P.IsReachable) (hE : P.IsExact F) :
    Nat.card (Quotient (resSetoid F)) ≤ Nat.card S :=
  Nat.card_le_card_of_surjective _ (toCanonical hR hE).surjective_toCanonical

end Canonical

end LikelyAllowed
