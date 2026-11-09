/-
Copyright (c) 2026 Joshua Matthew Carter. Released under the MIT-0 license.
Authors: Joshua Matthew Carter
-/
import LikelyAllowed.Residual
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Prop 2.7(b): finite tests suffice (Moore's bound)

If `ind(~_F) = k` with `2 ≤ k < ∞` then `~_F = ~^{Σ^{≤ k-2}}`; if `k = 1` then `~_F = ~^{∅}`.
Stated for an arbitrary codomain `X` (the paper states it for `V`).
-/

namespace LikelyAllowed

universe u v

variable {α : Type u} {X : Type v} (F : List α → X)

/-- The test equivalence `~^{Σ^{≤ j}}`. -/
def LenTest (j : ℕ) (h h' : List α) : Prop := TestEquiv F {z | z.length ≤ j} h h'

theorem lenTest_equivalence (j : ℕ) : Equivalence (LenTest F j) where
  refl _ _ _ := rfl
  symm H z hz := (H z hz).symm
  trans H H' z hz := (H z hz).trans (H' z hz)

/-- `~^{Σ^{≤ j}}` as a setoid. -/
def lenSetoid (j : ℕ) : Setoid (List α) := ⟨LenTest F j, lenTest_equivalence F j⟩

variable {F}

theorem LenTest.anti {i j : ℕ} (hij : i ≤ j) {h h' : List α} (H : LenTest F j h h') :
    LenTest F i h h' :=
  testEquiv_anti F (fun z (hz : z.length ≤ i) => (show z.length ≤ j by omega)) H

theorem ResEquiv.lenTest {h h' : List α} (H : ResEquiv F h h') (j : ℕ) : LenTest F j h h' :=
  H.testEquiv _

/-- `P_{j+1} = {(h,h') : h P_j h' ∧ he P_j h'e ∀ e}`. -/
theorem lenTest_succ_iff (j : ℕ) (h h' : List α) :
    LenTest F (j + 1) h h' ↔ LenTest F j h h' ∧ ∀ e, LenTest F j (h ++ [e]) (h' ++ [e]) := by
  constructor
  · intro H
    refine ⟨H.anti (Nat.le_succ j), fun e z hz => ?_⟩
    have hz' : z.length ≤ j := hz
    have := H (e :: z) (show (e :: z).length ≤ j + 1 by simp; omega)
    simpa [List.append_assoc] using this
  · rintro ⟨H1, H2⟩ z hz
    have hz' : z.length ≤ j + 1 := hz
    cases z with
    | nil => exact H1 [] (show [].length ≤ j by simp)
    | cons e z =>
      have := H2 e z (show z.length ≤ j by simp at hz'; omega)
      simpa [List.append_assoc] using this

/-- Once `P_j = P_{j+1}`, the chain is stable: `P_j ⊆ P_m` for all `m ≥ j`. -/
theorem lenTest_stable {j : ℕ} (hst : ∀ h h', LenTest F j h h' → LenTest F (j + 1) h h') :
    ∀ m, j ≤ m → ∀ h h', LenTest F j h h' → LenTest F m h h' := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact fun _ _ H => H
  | succ m hjm ih =>
    intro h h' H
    rw [lenTest_succ_iff]
    refine ⟨ih h h' H, fun e => ?_⟩
    -- `P_j ⊆ P_{j+1}` gives `he P_j h'e`, then `P_j ⊆ P_m`
    have H1 := (lenTest_succ_iff j h h').mp (hst h h' H)
    exact ih _ _ (H1.2 e)

/-- A stable level coincides with the residual equivalence. -/
theorem resEquiv_of_lenTest_stable {j : ℕ}
    (hst : ∀ h h', LenTest F j h h' → LenTest F (j + 1) h h') {h h' : List α}
    (H : LenTest F j h h') : ResEquiv F h h' := by
  intro z
  exact lenTest_stable hst (max j z.length) (le_max_left _ _) h h' H z
    (show z.length ≤ max j z.length from le_max_right _ _)

section Counting

variable [Finite (Quotient (resSetoid F))]

/-- The quotient map `Σ*/~_F → Σ*/P_j`. -/
def resToLen (j : ℕ) : Quotient (resSetoid F) → Quotient (lenSetoid F j) :=
  Quotient.lift (s := resSetoid F) (fun h => Quotient.mk (lenSetoid F j) h)
    (fun _ _ H => Quotient.sound (ResEquiv.lenTest (F := F) H j))

omit [Finite (Quotient (resSetoid F))] in
theorem resToLen_surjective (j : ℕ) : Function.Surjective (resToLen (F := F) j) := by
  intro q
  induction q using Quotient.ind with
  | _ h => exact ⟨Quotient.mk _ h, rfl⟩

instance finite_lenQuot (j : ℕ) : Finite (Quotient (lenSetoid F j)) :=
  Finite.of_surjective _ (resToLen_surjective j)

/-- The quotient map `Σ*/P_{j+1} → Σ*/P_j`. -/
def lenSuccToLen (j : ℕ) : Quotient (lenSetoid F (j + 1)) → Quotient (lenSetoid F j) :=
  Quotient.lift (s := lenSetoid F (j + 1)) (fun h => Quotient.mk (lenSetoid F j) h)
    (fun _ _ H => Quotient.sound (LenTest.anti (F := F) (Nat.le_succ j) H))

omit [Finite (Quotient (resSetoid F))] in
theorem lenSuccToLen_surjective (j : ℕ) : Function.Surjective (lenSuccToLen (F := F) j) := by
  intro q
  induction q using Quotient.ind with
  | _ h => exact ⟨Quotient.mk _ h, rfl⟩

theorem card_len_le_index (j : ℕ) :
    Nat.card (Quotient (lenSetoid F j)) ≤ Nat.card (Quotient (resSetoid F)) :=
  Nat.card_le_card_of_surjective _ (resToLen_surjective j)

/-- If the chain does not stabilize at `j`, the number of classes strictly increases. -/
theorem card_len_lt_of_not_stable (j : ℕ)
    (hns : ¬ ∀ h h', LenTest F j h h' → LenTest F (j + 1) h h') :
    Nat.card (Quotient (lenSetoid F j)) < Nat.card (Quotient (lenSetoid F (j + 1))) := by
  have hle := Nat.card_le_card_of_surjective _ (lenSuccToLen_surjective (F := F) j)
  refine lt_of_le_of_ne hle fun hc => hns fun h h' H => ?_
  have hbij := (Nat.bijective_iff_surjective_and_card (lenSuccToLen (F := F) j)).mpr
    ⟨lenSuccToLen_surjective j, hc.symm⟩
  have : Quotient.mk (lenSetoid F (j + 1)) h = Quotient.mk (lenSetoid F (j + 1)) h' :=
    hbij.1 (Quotient.sound H)
  exact Quotient.exact this

/-- If `ind(~_F) ≥ 2` then `P_0` has at least two classes. -/
theorem two_le_card_len_zero (hk : 2 ≤ Nat.card (Quotient (resSetoid F))) :
    2 ≤ Nat.card (Quotient (lenSetoid F 0)) := by
  by_contra hlt
  push Not at hlt
  have hsub : Subsingleton (Quotient (lenSetoid F 0)) :=
    (Finite.card_le_one_iff_subsingleton).mp (by omega)
  -- then `F` is constant, so all words are `~_F`-equivalent
  have hconst : ∀ h h', F h = F h' := by
    intro h h'
    have := Quotient.exact (Subsingleton.elim (Quotient.mk (lenSetoid F 0) h)
      (Quotient.mk (lenSetoid F 0) h'))
    simpa using this [] (show ([] : List α).length ≤ 0 by simp)
  have hsub' : Subsingleton (Quotient (resSetoid F)) := by
    constructor
    intro a b
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact Quotient.sound fun z => hconst _ _
  have := Finite.card_le_one_iff_subsingleton.mpr hsub'
  omega

/-- If the chain has not stabilized below `j`, then `P_j` has at least `j + 2` classes. -/
theorem card_len_ge (hk : 2 ≤ Nat.card (Quotient (resSetoid F))) (j : ℕ)
    (hns : ∀ i < j, ¬ ∀ h h', LenTest F i h h' → LenTest F (i + 1) h h') :
    j + 2 ≤ Nat.card (Quotient (lenSetoid F j)) := by
  induction j with
  | zero => simpa using two_le_card_len_zero hk
  | succ j ih =>
    have h1 := ih fun i hi => hns i (by omega)
    have h2 := card_len_lt_of_not_stable j (hns j (by omega))
    omega

/-- Paper Prop 2.7(b) (T6, Moore). If `ind(~_F) = k` with `2 ≤ k < ∞`, then
`~_F = ~^{Σ^{≤ k-2}}`. -/
theorem resEquiv_iff_lenTest (hk : 2 ≤ Nat.card (Quotient (resSetoid F))) (h h' : List α) :
    ResEquiv F h h' ↔ LenTest F (Nat.card (Quotient (resSetoid F)) - 2) h h' := by
  set k := Nat.card (Quotient (resSetoid F))
  refine ⟨fun H => H.lenTest _, fun H => ?_⟩
  -- some level `i ≤ k - 2` is stable
  have hex : ∃ i < k - 1, ∀ h h', LenTest F i h h' → LenTest F (i + 1) h h' := by
    by_contra hne
    push Not at hne
    have h1 := card_len_ge hk (k - 1) fun i hi hst => by
      obtain ⟨a, b, hab, hn⟩ := hne i hi
      exact hn (hst a b hab)
    have h2 := card_len_le_index (F := F) (k - 1)
    omega
  obtain ⟨i, hi, hst⟩ := hex
  exact resEquiv_of_lenTest_stable hst (H.anti (by omega))

/-- Paper Prop 2.7(b), case `k = 1`: `~_F = ~^{∅}` (all histories are
equivalent). -/
theorem resEquiv_of_index_one (hk : Nat.card (Quotient (resSetoid F)) = 1) (h h' : List α) :
    ResEquiv F h h' := by
  have : Subsingleton (Quotient (resSetoid F)) :=
    Finite.card_le_one_iff_subsingleton.mp hk.le
  exact Quotient.exact (Subsingleton.elim (Quotient.mk (resSetoid F) h) (Quotient.mk _ h'))

end Counting

end LikelyAllowed
