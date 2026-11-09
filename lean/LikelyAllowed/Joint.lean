/-
Copyright (c) 2026 Joshua Matthew Carter. Released under Apache 2.0 license.
Authors: Joshua Matthew Carter
-/
import LikelyAllowed.Residual
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Right congruences and joint equivalence (Paper Def 2.13, §4, Cor 4.3)
-/

namespace LikelyAllowed

universe u v v' w

variable {α : Type u} {X : Type v} {Y : Type v'}

/-- A relation on words is a *right congruence* if `h ~ h' ⇒ he ~ h'e` for every letter `e`. -/
def RightCongr (r : List α → List α → Prop) : Prop :=
  ∀ h h' e, r h h' → r (h ++ [e]) (h' ++ [e])

/-- A right congruence is compatible with appending arbitrary words: `h ~ h' ⇒ hz ~ h'z`. -/
theorem RightCongr.append {r : List α → List α → Prop} (hr : RightCongr r) {h h' : List α}
    (H : r h h') (z : List α) : r (h ++ z) (h' ++ z) := by
  induction z generalizing h h' with
  | nil => simpa using H
  | cons a z ih =>
    have := ih (hr h h' a H)
    simpa [List.append_assoc] using this

/-- Paper Lemma 2.2: `~_F` is a right congruence. -/
theorem resEquiv_rightCongr (F : List α → X) : RightCongr (ResEquiv F) :=
  fun _ _ e H => resEquiv_snoc H e

/-- Paper Def 2.13: the meet (intersection) of two right congruences is a right
congruence. -/
theorem RightCongr.inf {r s : List α → List α → Prop} (hr : RightCongr r) (hs : RightCongr s) :
    RightCongr (fun h h' => r h h' ∧ s h h') :=
  fun h h' e H => ⟨hr h h' e H.1, hs h h' e H.2⟩

/-- Paper Def 2.13: the joint equivalence `~_F ∩ ~_G`. -/
def JointEquiv (F : List α → X) (G : List α → Y) (h h' : List α) : Prop :=
  ResEquiv F h h' ∧ ResEquiv G h h'

/-- Paper Def 2.13: `~_F ∩ ~_G = ~_{(F,G)}`, the residual equivalence of the paired
semantics. -/
theorem jointEquiv_iff_resEquiv_pair (F : List α → X) (G : List α → Y) (h h' : List α) :
    JointEquiv F G h h' ↔ ResEquiv (fun w => (F w, G w)) h h' := by
  constructor
  · rintro ⟨H1, H2⟩ z
    simp [H1 z, H2 z]
  · intro H
    exact ⟨fun z => (Prod.ext_iff.mp (H z)).1, fun z => (Prod.ext_iff.mp (H z)).2⟩

/-- Paper Def 2.13: the joint equivalence is a right congruence. -/
theorem jointEquiv_rightCongr (F : List α → X) (G : List α → Y) :
    RightCongr (JointEquiv F G) :=
  (resEquiv_rightCongr F).inf (resEquiv_rightCongr G)

/-- Paper Def 2.13: the joint equivalence is an equivalence relation. -/
theorem jointEquiv_equivalence (F : List α → X) (G : List α → Y) :
    Equivalence (JointEquiv F G) where
  refl h := ⟨ResEquiv.refl F h, ResEquiv.refl G h⟩
  symm H := ⟨H.1.symm, H.2.symm⟩
  trans H H' := ⟨H.1.trans H'.1, H.2.trans H'.2⟩

/-- Paper Cor 4.3 (T8), general form: if the class maps of two equivalences `r₁`,
`r₂` on words are both functions of a statistic `s`, then `s` refines `r₁ ∩ r₂`. -/
theorem refines_inf_of_classes_factor {S : Type w} (r₁ r₂ : Setoid (List α))
    (s : List α → S)
    (h₁ : ∃ f₁ : S → Quotient r₁, ∀ h, Quotient.mk r₁ h = f₁ (s h))
    (h₂ : ∃ f₂ : S → Quotient r₂, ∀ h, Quotient.mk r₂ h = f₂ (s h))
    {h h' : List α} (hs : s h = s h') : r₁ h h' ∧ r₂ h h' := by
  obtain ⟨f₁, hf₁⟩ := h₁
  obtain ⟨f₂, hf₂⟩ := h₂
  exact ⟨Quotient.exact (by rw [hf₁, hf₁, hs]), Quotient.exact (by rw [hf₂, hf₂, hs])⟩

/-- Paper Cor 4.3 (T8), for residual equivalences: if the classes `[h]_F` and
`[h]_G` are both functions of `s`, then `s` refines the joint equivalence. -/
theorem refines_joint_of_classes_factor {S : Type w} (F : List α → X) (G : List α → Y)
    (s : List α → S)
    (hF : ∃ f : S → Quotient (resSetoid F), ∀ h, Quotient.mk _ h = f (s h))
    (hG : ∃ g : S → Quotient (resSetoid G), ∀ h, Quotient.mk _ h = g (s h))
    {h h' : List α} (hs : s h = s h') : JointEquiv F G h h' :=
  refines_inf_of_classes_factor (resSetoid F) (resSetoid G) s hF hG hs

/-- Paper Cor 4.3 (T8), residual-reading form: if both residuals `F_h`, `G_h` can be
read off `s h`, then `s` refines the joint equivalence. -/
theorem refines_joint_of_residuals_factor {S : Type w} (F : List α → X) (G : List α → Y)
    (s : List α → S)
    (hF : ∃ f : S → (List α → X), ∀ h, residual F h = f (s h))
    (hG : ∃ g : S → (List α → Y), ∀ h, residual G h = g (s h))
    {h h' : List α} (hs : s h = s h') : JointEquiv F G h h' :=
  ⟨(residual_factors_iff F s).mp hF h h' hs, (residual_factors_iff G s).mp hG h h' hs⟩

/-! ### Prop 4.2: the index sandwich (for arbitrary equivalences) -/

section Sandwich

variable {T : Type u} (r₁ r₂ : Setoid T)

/-- The class of `x` in the meet `r₁ ⊓ r₂` determines its classes in `r₁` and `r₂`. -/
def meetProj : Quotient (r₁ ⊓ r₂) → Quotient r₁ × Quotient r₂ :=
  Quotient.lift (s := r₁ ⊓ r₂) (fun x => (Quotient.mk r₁ x, Quotient.mk r₂ x))
    (fun _ _ H => by
      have H' := Setoid.inf_iff_and.mp H
      simp only [Prod.mk.injEq]
      exact ⟨Quotient.sound H'.1, Quotient.sound H'.2⟩)

theorem meetProj_injective : Function.Injective (meetProj r₁ r₂) := by
  intro a b hab
  induction a using Quotient.ind
  induction b using Quotient.ind
  simp only [meetProj, Quotient.lift_mk, Prod.mk.injEq] at hab
  exact Quotient.sound (Setoid.inf_iff_and.mpr ⟨Quotient.exact hab.1, Quotient.exact hab.2⟩)

/-- Projection from the meet's quotient onto the quotient by `r₁`. -/
def meetFst : Quotient (r₁ ⊓ r₂) → Quotient r₁ := fun q => (meetProj r₁ r₂ q).1

/-- Projection from the meet's quotient onto the quotient by `r₂`. -/
def meetSnd : Quotient (r₁ ⊓ r₂) → Quotient r₂ := fun q => (meetProj r₁ r₂ q).2

theorem meetFst_surjective : Function.Surjective (meetFst r₁ r₂) := by
  intro q
  induction q using Quotient.ind with
  | _ x => exact ⟨Quotient.mk _ x, rfl⟩

theorem meetSnd_surjective : Function.Surjective (meetSnd r₁ r₂) := by
  intro q
  induction q using Quotient.ind with
  | _ x => exact ⟨Quotient.mk _ x, rfl⟩

variable [Finite (Quotient r₁)] [Finite (Quotient r₂)]

instance finite_quotient_inf : Finite (Quotient (r₁ ⊓ r₂)) :=
  Finite.of_injective _ (meetProj_injective r₁ r₂)

/-- Paper Prop 4.2 (upper bound): `ind J ≤ ind ε · ind κ`. -/
theorem card_quotient_inf_le_mul :
    Nat.card (Quotient (r₁ ⊓ r₂)) ≤ Nat.card (Quotient r₁) * Nat.card (Quotient r₂) := by
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective _ (meetProj_injective r₁ r₂)

/-- Paper Prop 4.2 (lower bound): `max(ind ε, ind κ) ≤ ind J`. -/
theorem max_card_quotient_le_card_inf :
    max (Nat.card (Quotient r₁)) (Nat.card (Quotient r₂)) ≤ Nat.card (Quotient (r₁ ⊓ r₂)) :=
  max_le (Nat.card_le_card_of_surjective _ (meetFst_surjective r₁ r₂))
    (Nat.card_le_card_of_surjective _ (meetSnd_surjective r₁ r₂))

/-- Paper Prop 4.2: `ind J = ind κ ⇔ ~_κ ⊆ ~_ε` (here `r₂ = κ`, `r₁ = ε`). -/
theorem card_inf_eq_right_iff :
    Nat.card (Quotient (r₁ ⊓ r₂)) = Nat.card (Quotient r₂) ↔ ∀ x y, r₂ x y → r₁ x y := by
  constructor
  · intro hc x y hxy
    have hbij := (Nat.bijective_iff_surjective_and_card (meetSnd r₁ r₂)).mpr
      ⟨meetSnd_surjective r₁ r₂, hc⟩
    have : Quotient.mk (r₁ ⊓ r₂) x = Quotient.mk (r₁ ⊓ r₂) y :=
      hbij.1 (by simpa [meetSnd, meetProj] using Quotient.sound hxy)
    exact (Setoid.inf_iff_and.mp (Quotient.exact this)).1
  · intro H
    refine Nat.card_eq_of_bijective _ ⟨?_, meetSnd_surjective r₁ r₂⟩
    intro a b hab
    induction a using Quotient.ind with
    | _ x =>
    induction b using Quotient.ind with
    | _ y =>
    have hxy : r₂ x y := Quotient.exact (by simpa [meetSnd, meetProj] using hab)
    exact Quotient.sound (Setoid.inf_iff_and.mpr ⟨H x y hxy, hxy⟩)

/-- Paper Prop 4.2: `ind J = ind ε ⇔ ~_ε ⊆ ~_κ`. -/
theorem card_inf_eq_left_iff :
    Nat.card (Quotient (r₁ ⊓ r₂)) = Nat.card (Quotient r₁) ↔ ∀ x y, r₁ x y → r₂ x y := by
  rw [inf_comm]
  exact card_inf_eq_right_iff r₂ r₁

/-- Paper Prop 4.2: `ε` and `κ` are incomparable iff `ind J > max(ind ε, ind κ)`. -/
theorem incomparable_iff_max_lt :
    (¬ (∀ x y, r₁ x y → r₂ x y) ∧ ¬ (∀ x y, r₂ x y → r₁ x y)) ↔
      max (Nat.card (Quotient r₁)) (Nat.card (Quotient r₂)) < Nat.card (Quotient (r₁ ⊓ r₂)) := by
  rw [← card_inf_eq_left_iff, ← card_inf_eq_right_iff]
  have h1 := Nat.card_le_card_of_surjective _ (meetFst_surjective r₁ r₂)
  have h2 := Nat.card_le_card_of_surjective _ (meetSnd_surjective r₁ r₂)
  rw [max_lt_iff]
  omega

end Sandwich

end LikelyAllowed
