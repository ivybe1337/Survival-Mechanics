/-
Copyright (c) 2026 Joshua Matthew Carter. Released under Apache 2.0 license.
Authors: Joshua Matthew Carter
-/
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Setoid.Basic

/-!
# §2 Setting: semantics, residual congruence, admissibility rules

Words over an arbitrary alphabet `α` are `List α`; the empty word `Λ` is `[]` and
concatenation `hz` is `h ++ z`.  A *semantics* is any map `F : List α → X`.
-/

namespace LikelyAllowed

universe u v w

variable {α : Type u} {X : Type v}

/-! ### Def 2.1, Lemma 2.2 -/

/-- Paper Def 2.1. The residual `F_h : z ↦ F (h z)`. -/
def residual (F : List α → X) (h : List α) : List α → X := fun z => F (h ++ z)

/-- Paper Def 2.1. Residual equivalence: `h ~_F h'` iff `F_h = F_{h'}`. -/
def ResEquiv (F : List α → X) (h h' : List α) : Prop := ∀ z, F (h ++ z) = F (h' ++ z)

theorem resEquiv_iff_residual_eq {F : List α → X} {h h' : List α} :
    ResEquiv F h h' ↔ residual F h = residual F h' :=
  ⟨fun H => funext H, fun H z => congrFun H z⟩

/-- Paper Lemma 2.2 (T1): residual equivalence is an equivalence relation. -/
theorem resEquiv_equivalence (F : List α → X) : Equivalence (ResEquiv F) where
  refl _ _ := rfl
  symm H z := (H z).symm
  trans H H' z := (H z).trans (H' z)

theorem ResEquiv.refl (F : List α → X) (h : List α) : ResEquiv F h h := fun _ => rfl

theorem ResEquiv.symm {F : List α → X} {h h' : List α} (H : ResEquiv F h h') :
    ResEquiv F h' h := fun z => (H z).symm

theorem ResEquiv.trans {F : List α → X} {h h' h'' : List α} (H : ResEquiv F h h')
    (H' : ResEquiv F h' h'') : ResEquiv F h h'' := fun z => (H z).trans (H' z)

/-- The residual equivalence as a `Setoid` on words. -/
def resSetoid (F : List α → X) : Setoid (List α) := ⟨ResEquiv F, resEquiv_equivalence F⟩

@[simp] theorem resSetoid_r (F : List α → X) (h h' : List α) :
    (resSetoid F) h h' ↔ ResEquiv F h h' := Iff.rfl

/-- The residual equivalence at the empty continuation: `h ~_F h'` implies `F h = F h'`. -/
theorem ResEquiv.apply_eq {F : List α → X} {h h' : List α} (H : ResEquiv F h h') :
    F h = F h' := by
  simpa using H []

/-- Paper Lemma 2.2 (T2, right congruence, general form): `h ~_F h' ⇒ hz ~_F h'z`.
-/
theorem resEquiv_append_right {F : List α → X} {h h' : List α} (H : ResEquiv F h h')
    (z : List α) : ResEquiv F (h ++ z) (h' ++ z) := by
  intro y
  simpa [List.append_assoc] using H (z ++ y)

/-- Paper Lemma 2.2 (T2, right congruence, one-letter form): `h ~_F h' ⇒ he ~_F
h'e`. -/
theorem resEquiv_snoc {F : List α → X} {h h' : List α} (H : ResEquiv F h h') (e : α) :
    ResEquiv F (h ++ [e]) (h' ++ [e]) :=
  resEquiv_append_right H [e]

/-! ### Lemma 2.3: the coarsest statistic -/

/-- Paper Lemma 2.3 (T3). For a statistic `s : List α → S`, the residual `F_h` can
be read off `s h` (i.e. `F_h = g (s h)` for some `g`) iff `s h = s h' ⇒ h ~_F h'`. -/
theorem residual_factors_iff {S : Type w} (F : List α → X) (s : List α → S) :
    (∃ g : S → (List α → X), ∀ h, residual F h = g (s h)) ↔
      (∀ h h', s h = s h' → ResEquiv F h h') := by
  classical
  constructor
  · rintro ⟨g, hg⟩ h h' hs
    rw [resEquiv_iff_residual_eq, hg, hg, hs]
  · intro H
    refine ⟨fun σ => if hσ : ∃ h, s h = σ then residual F hσ.choose else residual F [], ?_⟩
    intro h
    have hex : ∃ h', s h' = s h := ⟨h, rfl⟩
    simp only [hex, ↓reduceDIte]
    exact resEquiv_iff_residual_eq.mp ((resEquiv_equivalence F).symm (H _ _ hex.choose_spec))

/-- Paper Lemma 2.3 ("hence"): the class map `h ↦ [h]_F` is itself a statistic
from which the residual can be read. -/
theorem residual_factors_through_class (F : List α → X) :
    ∃ g : Quotient (resSetoid F) → (List α → X),
      ∀ h, residual F h = g (Quotient.mk (resSetoid F) h) :=
  (residual_factors_iff F _).mpr fun _ _ hs => Quotient.exact hs

/-- Paper Lemma 2.3 ("coarsest"): any statistic from which the residual can be
read refines the class map, i.e. the class map factors through it. -/
theorem class_factors_through {S : Type w} (F : List α → X) (s : List α → S)
    (hs : ∃ g : S → (List α → X), ∀ h, residual F h = g (s h)) :
    ∃ f : S → Quotient (resSetoid F), ∀ h, f (s h) = Quotient.mk (resSetoid F) h := by
  classical
  have H := (residual_factors_iff F s).mp hs
  refine ⟨fun σ => if hσ : ∃ h, s h = σ then Quotient.mk _ hσ.choose else Quotient.mk _ [], ?_⟩
  intro h
  have hex : ∃ h', s h' = s h := ⟨h, rfl⟩
  simp only [hex, ↓reduceDIte]
  exact Quotient.sound (H _ _ hex.choose_spec)

/-! ### Def 2.4: admissibility rule -/

/-- Paper Def 2.4. The residual set, the admissible continuations `R_V(h) = {z | V (h z) = 1}`. -/
def resSet (V : List α → Bool) (h : List α) : Set (List α) := {z | V (h ++ z) = true}

/-- Paper Def 2.4. `V` is *monotone* (a admissibility rule proper): `V(hz) = 1 ⇒
V(h) = 1`. -/
def AdmMonotone (V : List α → Bool) : Prop := ∀ h z, V (h ++ z) = true → V h = true

/-- For Boolean semantics, `h ~_V h'` iff `R_V(h) = R_V(h')` (Paper Def 2.4, `R_V(h)
≅ V_h`). -/
theorem resEquiv_iff_resSet_eq {V : List α → Bool} {h h' : List α} :
    ResEquiv V h h' ↔ resSet V h = resSet V h' := by
  constructor
  · intro H
    ext z
    simp [resSet, H z]
  · intro H z
    have hz : z ∈ resSet V h ↔ z ∈ resSet V h' := by rw [H]
    simp only [resSet, Set.mem_ofPred_eq] at hz
    cases h1 : V (h ++ z) <;> cases h2 : V (h' ++ z) <;> simp_all

/-! ### Prop 2.5: totalization is conservative -/

/-- A set of words is prefix-closed. -/
def PrefixClosed (H : Set (List α)) : Prop := ∀ w z, w ++ z ∈ H → w ∈ H

/-- Paper Prop 2.6. Totalization `V̄` of a partial admissibility rule `V_H : H →
{0,1}` (given as a function on all words, only its values on `H` matter). -/
def totalize (H : Set (List α)) [DecidablePred (· ∈ H)] (VH : List α → Bool) :
    List α → Bool :=
  fun w => if w ∈ H then VH w else false

section Totalize
variable (H : Set (List α)) [DecidablePred (· ∈ H)] (VH : List α → Bool)

/-- Paper Prop 2.6(a). For `h ∈ H`, `R_{V̄}(h) = {z | hz ∈ H ∧ V_H(hz) = 1}`. -/
theorem resSet_totalize_of_mem {h : List α} (_hh : h ∈ H) :
    resSet (totalize H VH) h = {z | h ++ z ∈ H ∧ VH (h ++ z) = true} := by
  ext z
  simp only [resSet, totalize, Set.mem_ofPred_eq]
  split_ifs with hz <;> simp [hz]

/-- Paper Prop 2.6(b). For `h ∉ H` (with `H` prefix-closed), `R_{V̄}(h) = ∅`. -/
theorem resSet_totalize_of_not_mem (hH : PrefixClosed H) {h : List α} (hh : h ∉ H) :
    resSet (totalize H VH) h = ∅ := by
  ext z
  simp only [resSet, totalize, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  split_ifs with hz
  · exact absurd (hH _ _ hz) hh
  · simp

/-- Paper Prop 2.6(c). If `V_H` is monotone on `H` then `V̄` is monotone. -/
theorem admMonotone_totalize (hH : PrefixClosed H)
    (hmono : ∀ h z, h ++ z ∈ H → VH (h ++ z) = true → VH h = true) :
    AdmMonotone (totalize H VH) := by
  intro h z hz
  simp only [totalize] at hz ⊢
  split_ifs at hz with hmem
  · simp only [hH _ _ hmem, ↓reduceIte]
    exact hmono h z hmem hz
end Totalize

/-! ### Lemma 2.6: the dead class -/

section Dead
variable {V : List α → Bool}

/-- Paper Lemma 2.5. Any two histories with empty residual are equivalent. -/
theorem resEquiv_of_resSet_empty {h h' : List α} (hh : resSet V h = ∅)
    (hh' : resSet V h' = ∅) : ResEquiv V h h' :=
  resEquiv_iff_resSet_eq.mpr (hh.trans hh'.symm)

/-- Paper Lemma 2.5. The dead histories form a single `~_V` class: if `h` is dead
then `h ~_V h'` iff `h'` is dead. -/
theorem resEquiv_dead_iff {h : List α} (hh : resSet V h = ∅) (h' : List α) :
    ResEquiv V h h' ↔ resSet V h' = ∅ := by
  constructor
  · intro H; rw [← resEquiv_iff_resSet_eq.mp H, hh]
  · exact resEquiv_of_resSet_empty hh

/-- Paper Lemma 2.5. The dead class is absorbing: `R_V(h) = ∅ ⇒ R_V(hz) = ∅`. -/
theorem resSet_append_empty {h : List α} (hh : resSet V h = ∅) (z : List α) :
    resSet V (h ++ z) = ∅ := by
  ext y
  have : (z ++ y) ∉ resSet V h := by rw [hh]; exact id
  simpa [resSet, List.append_assoc] using this

/-- Paper Lemma 2.5. For monotone `V`, `R_V(h) = ∅ ⇔ V(h) = 0`. -/
theorem resSet_empty_iff (hV : AdmMonotone V) (h : List α) :
    resSet V h = ∅ ↔ V h = false := by
  constructor
  · intro hh
    have : ([] : List α) ∉ resSet V h := by rw [hh]; exact id
    simpa [resSet] using this
  · intro hh
    ext z
    simp only [resSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hz
    have := hV h z hz
    simp_all
end Dead

/-! ### Prop 2.7(a): finite tests -/

/-- Paper Prop 2.7. Test equivalence `h ~^Z h'` iff `V(hz) = V(h'z)` for all `z ∈
Z`. -/
def TestEquiv (F : List α → X) (Z : Set (List α)) (h h' : List α) : Prop :=
  ∀ z ∈ Z, F (h ++ z) = F (h' ++ z)

/-- Paper Prop 2.7(a). `Z ⊆ Z' ⇒ ~^{Z'} ⊆ ~^{Z}`. -/
theorem testEquiv_anti (F : List α → X) {Z Z' : Set (List α)} (hZ : Z ⊆ Z')
    {h h' : List α} (H : TestEquiv F Z' h h') : TestEquiv F Z h h' :=
  fun z hz => H z (hZ hz)

/-- Paper Prop 2.7(a). `~_V = ~^{Σ*}`. -/
theorem testEquiv_univ_iff (F : List α → X) (h h' : List α) :
    TestEquiv F Set.univ h h' ↔ ResEquiv F h h' :=
  ⟨fun H z => H z trivial, fun H z _ => H z⟩

/-- Paper Prop 2.7(a). The residual equivalence refines every test equivalence.
-/
theorem ResEquiv.testEquiv {F : List α → X} {h h' : List α} (H : ResEquiv F h h')
    (Z : Set (List α)) : TestEquiv F Z h h' :=
  fun z _ => H z

end LikelyAllowed
