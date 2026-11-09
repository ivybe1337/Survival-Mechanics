/-
Copyright (c) 2026 Joshua Matthew Carter. Released under Apache 2.0 license.
Authors: Joshua Matthew Carter
-/
import LikelyAllowed.Conditioned
import LikelyAllowed.Nondet

/-!
# Paper Proposition 6.2: lookahead feasibility is 1-Lipschitz

`A^{(k)}(h) = {e : ∃ z, |z| ≤ k - 1, V(hez) = 1}` (`k ≥ 1`), `A^{(0)}(h) = ∅`, and
`R^{(k)}(h) = R_V(h) ∩ Σ^{≤ k}`. Then
`|A^{(k)}(h) △ A^{(k)}(h')| ≤ min(|Σ|, |(R^{(k)}(h) △ R^{(k)}(h')) ∖ {Λ}|)`.
-/

namespace LikelyAllowed

open Finset

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- `Σ^{≤ k}` as a `Finset`. -/
def wordsLE (α : Type u) [Fintype α] [DecidableEq α] (k : ℕ) : Finset (List α) :=
  (range (k + 1)).biUnion (words α)

theorem mem_wordsLE {k : ℕ} {w : List α} : w ∈ wordsLE α k ↔ w.length ≤ k := by
  simp [wordsLE, mem_words]

/-- Paper §6.2: the `k`-step lookahead feasible set `A^{(k)}(h)`. -/
noncomputable def lookA (V : List α → Bool) (k : ℕ) (h : List α) : Finset α := by
  classical
  exact if k = 0 then ∅ else univ.filter fun e => ∃ z : List α, z.length ≤ k - 1 ∧
    V (h ++ e :: z) = true

/-- Paper §6.2: `R^{(k)}(h) = R_V(h) ∩ Σ^{≤ k}`. -/
def lookR (V : List α → Bool) (k : ℕ) (h : List α) : Finset (List α) :=
  (wordsLE α k).filter fun z => V (h ++ z) = true

omit [DecidableEq α] in
theorem mem_lookA {V : List α → Bool} {k : ℕ} {h : List α} {e : α} :
    e ∈ lookA V k h ↔ k ≠ 0 ∧ ∃ z : List α, z.length ≤ k - 1 ∧ V (h ++ e :: z) = true := by
  unfold lookA
  split_ifs with hk <;> simp [hk]

theorem mem_lookR {V : List α → Bool} {k : ℕ} {h z : List α} :
    z ∈ lookR V k h ↔ z.length ≤ k ∧ V (h ++ z) = true := by
  simp [lookR, mem_wordsLE]

/-- Paper Prop 6.2 (1-Lipschitz lookahead feasibility). -/
theorem card_lookA_symmDiff_le (V : List α → Bool) (k : ℕ) (h h' : List α) :
    #(symmDiff (lookA V k h) (lookA V k h')) ≤
      min (Fintype.card α) #((symmDiff (lookR V k h) (lookR V k h')) \ {[]}) := by
  classical
  refine le_min (card_le_univ _) ?_
  -- witness continuation for `e ∈ A^{(k)}(g)`
  let wit : List α → α → List α := fun g e =>
    if H : ∃ z : List α, z.length ≤ k - 1 ∧ V (g ++ e :: z) = true then H.choose else []
  have hwit : ∀ g e, e ∈ lookA V k g →
      (wit g e).length ≤ k - 1 ∧ V (g ++ e :: wit g e) = true ∧ k ≠ 0 := by
    intro g e he
    obtain ⟨hk, H⟩ := mem_lookA.mp he
    simp only [wit, H, ↓reduceDIte]
    exact ⟨H.choose_spec.1, H.choose_spec.2, hk⟩
  let f : α → List α := fun e => if e ∈ lookA V k h then e :: wit h e else e :: wit h' e
  refine card_le_card_of_injOn f ?_ ?_
  · intro e he
    have he' := mem_symmDiff.mp (mem_coe.mp he)
    rw [mem_coe, mem_sdiff, mem_symmDiff, mem_singleton]
    refine ⟨?_, by simp only [f]; split_ifs <;> simp⟩
    rcases he' with ⟨hA, hA'⟩ | ⟨hA', hA⟩
    · obtain ⟨hl, hV, hk⟩ := hwit h e hA
      simp only [f, hA, ↓reduceIte]
      refine Or.inl ⟨mem_lookR.mpr ⟨by simp; omega, hV⟩, fun hR => hA' ?_⟩
      exact mem_lookA.mpr ⟨hk, wit h e, hl, (mem_lookR.mp hR).2⟩
    · obtain ⟨hl, hV, hk⟩ := hwit h' e hA'
      simp only [f, hA, ↓reduceIte]
      refine Or.inr ⟨mem_lookR.mpr ⟨by simp; omega, hV⟩, fun hR => hA ?_⟩
      exact mem_lookA.mpr ⟨hk, wit h' e, hl, (mem_lookR.mp hR).2⟩
  · intro e _ e' _ hee
    simp only [f] at hee
    split_ifs at hee <;> exact (List.cons.inj hee).1

/-! ### Tightness (Paper Prop 6.2, "both terms of the minimum are attained") -/

theorem lookA_nil_noBB {k : ℕ} (hk : k ≠ 0) : lookA noBB k [] = univ := by
  ext e
  simp only [mem_lookA, mem_univ, iff_true]
  exact ⟨hk, [], by simp, by cases e <;> rfl⟩

theorem lookA_bb_noBB (k : ℕ) : lookA noBB k [true, true] = ∅ := by
  ext e
  simp only [mem_lookA, Finset.notMem_empty, iff_false, not_and, not_exists]
  intro _ z _
  simp [noBB]

/-- Paper Prop 6.2, first term attained: for `V_bb`, `h = Λ`, `h' = bb`, every `k ≥ 1`. -/
theorem lookahead_tight_card (k : ℕ) (hk : k ≠ 0) :
    #(symmDiff (lookA noBB k []) (lookA noBB k [true, true])) = Fintype.card Bool := by
  rw [lookA_nil_noBB hk, lookA_bb_noBB]
  decide

theorem lookA_b_noBB : lookA noBB 1 [true] = {false} := by
  ext e
  simp only [mem_lookA, mem_singleton]
  constructor
  · rintro ⟨-, z, hz, hV⟩
    have hz0 : z = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hz0
    cases e
    · rfl
    · simp [noBB] at hV
  · rintro rfl
    exact ⟨one_ne_zero, [], by simp, rfl⟩

theorem lookR_diff_noBB :
    (symmDiff (lookR noBB 1 []) (lookR noBB 1 [true])) \ {[]} = {[true]} := by
  ext z
  simp only [mem_sdiff, mem_symmDiff, mem_lookR, mem_singleton, List.nil_append,
    List.singleton_append]
  match z with
  | [] => simp
  | [false] => simp [noBB]
  | [true] => simp [noBB]
  | _ :: _ :: _ => simp

/-- Paper Prop 6.2, second term attained: for `V_bb`, `h = Λ`, `h' = b`, `k = 1`, both sides
equal `1`. -/
theorem lookahead_tight_residual :
    #(symmDiff (lookA noBB 1 []) (lookA noBB 1 [true])) = 1 ∧
      #((symmDiff (lookR noBB 1 []) (lookR noBB 1 [true])) \ {[]}) = 1 := by
  refine ⟨?_, by rw [lookR_diff_noBB]; rfl⟩
  rw [lookA_nil_noBB one_ne_zero, lookA_b_noBB]
  decide

end LikelyAllowed
