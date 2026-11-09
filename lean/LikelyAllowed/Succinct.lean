/-
Copyright (c) 2026 Joshua Matthew Carter. Released under the MIT-0 license.
Authors: Joshua Matthew Carter
-/
import LikelyAllowed.Nondet
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi

/-!
# Paper Theorem 8.6: exponential succinctness, exactly

`V_n(w) = 0` iff `w` has an `a` followed exactly `n - 1` positions later by a `b`
(`a = false`, `b = true`). For `n ≥ 2`:
(a) `ind(V_n) = 2^{n-1} + 1`;
(b) the minimum number of states of an exact universal presentation of `V_n` is `n + 1`.
-/

namespace LikelyAllowed

open Finset

/-! ### Word lemmas -/

theorem getElem?_snoc_lt {α : Type*} {h : List α} {e : α} {j : ℕ} (hj : j < h.length) :
    (h ++ [e])[j]? = h[j]? :=
  List.getElem?_append_left hj

theorem getElem?_snoc_len {α : Type*} (h : List α) (e : α) : (h ++ [e])[h.length]? = some e := by
  simp

theorem getElem?_snoc_gt {α : Type*} {h : List α} {e : α} {j : ℕ} (hj : h.length < j) :
    (h ++ [e])[j]? = none := by
  rw [List.getElem?_append_right (by omega)]
  simp
  omega

/-- The death pattern of `V_n`: an `a` at position `i` and a `b` at position `i + n - 1`. -/
def Bad (n : ℕ) (w : List Bool) : Prop := ∃ i, w[i]? = some false ∧ w[i + (n - 1)]? = some true

open Classical in
/-- Paper Thm 8.6: `V_n(w) = 1` iff `w` has no `a` followed exactly `n - 1` positions later by
a `b`. -/
noncomputable def Vn (n : ℕ) (w : List Bool) : Bool := decide (¬ Bad n w)

theorem Vn_eq_true_iff {n : ℕ} {w : List Bool} : Vn n w = true ↔ ¬ Bad n w := by simp [Vn]

theorem not_bad_nil (n : ℕ) : ¬ Bad n [] := by
  rintro ⟨i, h1, -⟩; simp at h1

theorem not_bad_replicate_true (n k : ℕ) : ¬ Bad n (List.replicate k true) := by
  rintro ⟨i, h1, -⟩
  rw [List.getElem?_replicate] at h1
  split_ifs at h1
  simp at h1

theorem not_bad_of_length_lt {n : ℕ} {w : List Bool} (hw : w.length < n) : ¬ Bad n w := by
  rintro ⟨i, -, h2⟩
  have := (List.getElem?_eq_some_iff.mp h2).1
  omega

theorem bad_a_bs {n : ℕ} (hn : 2 ≤ n) : Bad n (false :: List.replicate (n - 1) true) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  refine ⟨0, rfl, ?_⟩
  simp

/-- Appending a letter creates the pattern exactly at the new last position. -/
theorem bad_snoc {n : ℕ} (hn : 2 ≤ n) (h : List Bool) (e : Bool) :
    Bad n (h ++ [e]) ↔
      Bad n h ∨ (e = true ∧ n - 1 ≤ h.length ∧ h[h.length - (n - 1)]? = some false) := by
  constructor
  · rintro ⟨i, h1, h2⟩
    rcases lt_trichotomy (i + (n - 1)) h.length with c | c | c
    · left
      rw [getElem?_snoc_lt c] at h2
      rw [getElem?_snoc_lt (by omega)] at h1
      exact ⟨i, h1, h2⟩
    · right
      rw [c, getElem?_snoc_len] at h2
      rw [getElem?_snoc_lt (by omega)] at h1
      refine ⟨by simpa using h2, by omega, ?_⟩
      rwa [show h.length - (n - 1) = i by omega]
    · rw [getElem?_snoc_gt c] at h2
      simp at h2
  · rintro (⟨i, h1, h2⟩ | ⟨he, hl, h3⟩)
    · have c := (List.getElem?_eq_some_iff.mp h2).1
      refine ⟨i, ?_, ?_⟩
      · rw [getElem?_snoc_lt (by omega)]; exact h1
      · rw [getElem?_snoc_lt c]; exact h2
    · refine ⟨h.length - (n - 1), ?_, ?_⟩
      · rw [getElem?_snoc_lt (by omega)]; exact h3
      · rw [show h.length - (n - 1) + (n - 1) = h.length by omega, getElem?_snoc_len, he]

/-! ### Part (b), upper bound: the universal presentation `U_n` -/

/-- Transition relation of `U_n` on state indices:
`δ(0,a) = {0,1}`, `δ(0,b) = {0}`, `δ(i,·) = {i+1}` (`1 ≤ i ≤ n-2`), `δ(n-1,a) = {0}`,
`δ(n-1,b) = {n}`, `δ(n,·) = {n}`. -/
def UR (n s t : ℕ) (e : Bool) : Prop :=
  (s = 0 ∧ t = 0) ∨ (s = 0 ∧ t = 1 ∧ e = false) ∨ (1 ≤ s ∧ s + 2 ≤ n ∧ t = s + 1) ∨
    (s = n - 1 ∧ e = false ∧ t = 0) ∨ (s = n - 1 ∧ e = true ∧ t = n) ∨ (s = n ∧ t = n)

instance (n s t : ℕ) (e : Bool) : Decidable (UR n s t e) := by unfold UR; infer_instance

/-- The transition sets of `U_n`. -/
def Uδ (n : ℕ) (s : Fin (n + 1)) (e : Bool) : Finset (Fin (n + 1)) :=
  univ.filter fun t => UR n s.val t.val e

theorem mem_Uδ {n : ℕ} {s t : Fin (n + 1)} {e : Bool} : t ∈ Uδ n s e ↔ UR n s.val t.val e := by
  simp [Uδ]

/-- Paper Thm 8.6(b): the `(n+1)`-state universal presentation `U_n` (`ℓ(n) = 0`, else `1`). -/
def Un (n : ℕ) : UPres Bool (Fin (n + 1)) where
  start := 0
  δ := Uδ n
  δ_nonempty s e := by
    by_cases h0 : s.val = 0
    · exact ⟨0, mem_Uδ.mpr (Or.inl ⟨h0, rfl⟩)⟩
    by_cases h1 : s.val + 2 ≤ n
    · exact ⟨⟨s.val + 1, by omega⟩, mem_Uδ.mpr (Or.inr (Or.inr (Or.inl ⟨by omega, h1, rfl⟩)))⟩
    by_cases h2 : s.val = n - 1
    · cases e
      · exact ⟨0, mem_Uδ.mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, rfl, rfl⟩))))⟩
      · exact ⟨Fin.last n,
          mem_Uδ.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, rfl, rfl⟩)))))⟩
    · exact ⟨Fin.last n, mem_Uδ.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨by have := s.isLt; omega, rfl⟩)))))⟩
  ℓ t := decide (t.val ≠ n)

/-- Invariant of `U_n`: `0` is always reached; `1 ≤ i ≤ n-1` is reached iff the `i`-th symbol
from the end is `a`; `n` is reached iff the history is dead. -/
def UInv (n : ℕ) (h : List Bool) (t : ℕ) : Prop :=
  t = 0 ∨ (1 ≤ t ∧ t ≤ n - 1 ∧ t ≤ h.length ∧ h[h.length - t]? = some false) ∨
    (t = n ∧ Bad n h)

theorem UInv_snoc_of {n : ℕ} (hn : 2 ≤ n) {h : List Bool} {e : Bool} {s t : ℕ}
    (hs : UInv n h s) (hR : UR n s t e) : UInv n (h ++ [e]) t := by
  rcases hR with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · refine Or.inr (Or.inl ⟨le_rfl, by omega, by simp, ?_⟩)
    rw [List.length_append, List.length_singleton, Nat.add_sub_cancel, getElem?_snoc_len]
  · rcases hs with hs | ⟨-, -, hsl, hget⟩ | ⟨hs, -⟩
    · omega
    · refine Or.inr (Or.inl ⟨by omega, by omega, by simp; omega, ?_⟩)
      rw [List.length_append, List.length_singleton,
        show h.length + 1 - (s + 1) = h.length - s by omega, getElem?_snoc_lt (by omega)]
      exact hget
    · omega
  · exact Or.inl rfl
  · rcases hs with hs | ⟨-, -, hl, hget⟩ | ⟨hs, -⟩
    · omega
    · exact Or.inr (Or.inr ⟨rfl, (bad_snoc hn h true).mpr (Or.inr ⟨rfl, hl, hget⟩)⟩)
    · omega
  · rcases hs with hs | ⟨-, hs, -⟩ | ⟨-, hbad⟩
    · omega
    · omega
    · exact Or.inr (Or.inr ⟨rfl, (bad_snoc hn h e).mpr (Or.inl hbad)⟩)

theorem exists_of_UInv_snoc {n : ℕ} (hn : 2 ≤ n) {h : List Bool} {e : Bool} {t : ℕ}
    (ht : UInv n (h ++ [e]) t) : ∃ s, s ≤ n ∧ UInv n h s ∧ UR n s t e := by
  rcases ht with rfl | ⟨h1, h2, h3, hget⟩ | ⟨htn, hbad⟩
  · exact ⟨0, by omega, Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
  · simp only [List.length_append, List.length_singleton] at h3 hget
    by_cases ht1 : t = 1
    · subst ht1
      rw [Nat.add_sub_cancel, getElem?_snoc_len] at hget
      have he : e = false := by simpa using hget
      exact ⟨0, by omega, Or.inl rfl, Or.inr (Or.inl ⟨rfl, rfl, he⟩)⟩
    · rw [getElem?_snoc_lt (by omega)] at hget
      refine ⟨t - 1, by omega, Or.inr (Or.inl ⟨by omega, by omega, by omega, ?_⟩),
        Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))⟩
      rwa [show h.length - (t - 1) = h.length + 1 - t by omega]
  · rw [htn]
    rcases (bad_snoc hn h e).mp hbad with hb | ⟨he, hl, hget⟩
    · exact ⟨n, le_rfl, Or.inr (Or.inr ⟨rfl, hb⟩), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨rfl, rfl⟩))))⟩
    · exact ⟨n - 1, by omega, Or.inr (Or.inl ⟨by omega, le_rfl, hl, hget⟩),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, he, rfl⟩))))⟩

theorem Un_reach {n : ℕ} (hn : 2 ≤ n) (h : List Bool) (t : Fin (n + 1)) :
    t ∈ (Un n).Reach h ↔ UInv n h t.val := by
  induction h using List.reverseRecOn generalizing t with
  | nil =>
    simp only [UPres.Reach, UPres.runSet_nil, mem_singleton]
    constructor
    · rintro rfl; exact Or.inl rfl
    · rintro (h0 | ⟨h1, -, h3, -⟩ | ⟨-, hb⟩)
      · exact Fin.ext h0
      · exfalso
        simp only [List.length_nil] at h3
        omega
      · exact absurd hb (not_bad_nil n)
  | append_singleton h e ih =>
    rw [UPres.Reach_snoc, UPres.img, mem_biUnion]
    constructor
    · rintro ⟨s, hs, ht⟩
      exact UInv_snoc_of hn ((ih s).mp hs) (mem_Uδ.mp ht)
    · intro ht
      obtain ⟨s, hsn, hs, hR⟩ := exists_of_UInv_snoc hn ht
      exact ⟨⟨s, by omega⟩, (ih _).mpr hs, mem_Uδ.mpr hR⟩

/-- Paper Thm 8.6(b): `U_n` is exact for `V_n` (for all words). -/
theorem Un_exact {n : ℕ} (hn : 2 ≤ n) : (Un n).IsExact (Vn n) := by
  intro h
  rw [Vn_eq_true_iff]
  constructor
  · intro hsafe hbad
    have hmem : Fin.last n ∈ (Un n).Reach h :=
      (Un_reach hn h _).mpr (Or.inr (Or.inr ⟨rfl, hbad⟩))
    have := hsafe _ hmem
    simp [Un] at this
  · intro hbad t ht
    have hinv := (Un_reach hn h t).mp ht
    simp only [Un, decide_eq_true_eq]
    intro htn
    rcases hinv with h0 | ⟨-, h2, -⟩ | ⟨-, hb⟩
    · omega
    · omega
    · exact hbad hb

/-! ### Part (b), lower bound: the fooling set -/

/-- Prefixes of the fooling set: `Λ, a, ab, …, ab^{n-1}`. -/
def foolXn (_n : ℕ) (i : Fin (_n + 1)) : List Bool :=
  if i.val = 0 then [] else false :: List.replicate (i.val - 1) true

/-- Suffixes of the fooling set: `ab^{n-1}, b^{n-1}, …, b, Λ`. -/
def foolYn (n : ℕ) (i : Fin (n + 1)) : List Bool :=
  if i.val = 0 then false :: List.replicate (n - 1) true else List.replicate (n - i.val) true

theorem foolXn_append_foolYn {n : ℕ} (i : Fin (n + 1)) :
    foolXn n i ++ foolYn n i = false :: List.replicate (n - 1) true := by
  unfold foolXn foolYn
  split_ifs with h0
  · rfl
  · rw [List.cons_append, List.replicate_append_replicate]
    congr 2
    have := i.isLt
    omega

theorem Vn_fool_off {n : ℕ} {i j : Fin (n + 1)} (hij : i.val < j.val) :
    Vn n (foolXn n i ++ foolYn n j) = true := by
  rw [Vn_eq_true_iff]
  unfold foolXn foolYn
  have hj0 : j.val ≠ 0 := by omega
  simp only [hj0, ↓reduceIte]
  split_ifs with hi0
  · simpa using not_bad_replicate_true n (n - j.val)
  · apply not_bad_of_length_lt
    have := j.isLt
    simp
    omega

/-- Paper Thm 8.6(b), lower bound: every exact universal presentation of `V_n` has at least
`n + 1` states (fooling set `(Λ, ab^{n-1}), (ab^{i-1}, b^{n-i}), (ab^{n-1}, Λ)`). -/
theorem Vn_card_ge {n : ℕ} (hn : 2 ≤ n) {S : Type*} [Fintype S] [DecidableEq S]
    (Q : UPres Bool S) (hQ : Q.IsExact (Vn n)) : n + 1 ≤ Fintype.card S := by
  have := hQ.card_ge_of_fooling (foolXn n) (foolYn n)
    (fun i => by
      rw [foolXn_append_foolYn]
      exact Bool.eq_false_iff.mpr fun h => (Vn_eq_true_iff.mp h) (bad_a_bs hn))
    (fun i j hij => by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · exact Or.inl (Vn_fool_off h)
      · exact Or.inr (Vn_fool_off h))
  simpa using this

/-- Paper Thm 8.6(b): the minimum number of states of an exact universal presentation of `V_n`
is `n + 1`. -/
theorem Vn_min_universal_size {n : ℕ} (hn : 2 ≤ n) :
    (Un n).IsExact (Vn n) ∧ Fintype.card (Fin (n + 1)) = n + 1 ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S] (Q : UPres Bool S),
        Q.IsExact (Vn n) → n + 1 ≤ Fintype.card S :=
  ⟨Un_exact hn, Fintype.card_fin _, fun _ _ _ Q hQ => Vn_card_ge hn Q hQ⟩

/-! ### Part (a): `ind(V_n) = 2^{n-1} + 1` -/

open Classical in
/-- The residual state of `V_n`: dead (`none`), or alive with the set `W(h)` of `i ∈ [1, n-1]`
such that the `i`-th symbol from the end is `a` (encoded by `j = i - 1 : Fin (n - 1)`). -/
noncomputable def σn (n : ℕ) (h : List Bool) : Option (Fin (n - 1) → Bool) :=
  if Bad n h then none
  else some fun j => decide (j.val < h.length ∧ h[h.length - 1 - j.val]? = some false)

theorem Vn_eq_isSome (n : ℕ) (h : List Bool) : Vn n h = (σn n h).isSome := by
  unfold Vn σn
  split_ifs with hb <;> simp [hb]

/-- Transition of the residual state. -/
noncomputable def σstep (n : ℕ) : Option (Fin (n - 1) → Bool) → Bool → Option (Fin (n - 1) → Bool)
  | none, _ => none
  | some f, e =>
    open Classical in
    if e = true ∧ ∃ j : Fin (n - 1), j.val = n - 2 ∧ f j = true then none
    else some fun j => if hj : j.val = 0 then !e else f ⟨j.val - 1, by omega⟩

theorem σn_snoc {n : ℕ} (hn : 2 ≤ n) (h : List Bool) (e : Bool) :
    σn n (h ++ [e]) = σstep n (σn n h) e := by
  by_cases hb : Bad n h
  · have hb' : Bad n (h ++ [e]) := (bad_snoc hn h e).mpr (Or.inl hb)
    simp [σn, hb, hb', σstep]
  by_cases hd : e = true ∧ n - 1 ≤ h.length ∧ h[h.length - (n - 1)]? = some false
  · have hb' : Bad n (h ++ [e]) := (bad_snoc hn h e).mpr (Or.inr hd)
    have hcond : e = true ∧ ∃ j : Fin (n - 1), j.val = n - 2 ∧
        decide (j.val < h.length ∧ h[h.length - 1 - j.val]? = some false) = true := by
      refine ⟨hd.1, ⟨⟨n - 2, by omega⟩, rfl, ?_⟩⟩
      simp only [decide_eq_true_eq]
      refine ⟨by omega, ?_⟩
      rw [show h.length - 1 - (n - 2) = h.length - (n - 1) by omega]
      exact hd.2.2
    have e1 : σn n (h ++ [e]) = none := by unfold σn; simp only [hb', ↓reduceIte]
    have e2 : σn n h = some fun j =>
        decide (j.val < h.length ∧ h[h.length - 1 - j.val]? = some false) := by
      unfold σn; simp only [hb, ↓reduceIte]
    rw [e1, e2]
    simp only [σstep]
    split_ifs
    rfl
  · have hb' : ¬ Bad n (h ++ [e]) := by
      rw [bad_snoc hn h e]; exact fun H => H.elim hb hd
    have hcond : ¬ (e = true ∧ ∃ j : Fin (n - 1), j.val = n - 2 ∧
        decide (j.val < h.length ∧ h[h.length - 1 - j.val]? = some false) = true) := by
      rintro ⟨he, j, hj, hfj⟩
      simp only [decide_eq_true_eq] at hfj
      refine hd ⟨he, by omega, ?_⟩
      rw [show h.length - (n - 1) = h.length - 1 - j.val by omega]
      exact hfj.2
    simp only [σn, hb, hb', ↓reduceIte, σstep, hcond, Option.some.injEq]
    funext j
    simp only [List.length_append, List.length_singleton]
    by_cases hj : j.val = 0
    · simp only [hj, ↓reduceDIte, Nat.add_sub_cancel, Nat.sub_zero, getElem?_snoc_len]
      cases e <;> simp
    · simp only [hj, ↓reduceDIte]
      by_cases hjl : j.val ≤ h.length
      · rw [show h.length + 1 - 1 - j.val = h.length - 1 - (j.val - 1) by omega,
          getElem?_snoc_lt (by omega)]
        congr 1
        apply propext
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
      · have h1 : ¬ (j.val < h.length + 1) := by omega
        have h2 : ¬ (j.val - 1 < h.length) := by omega
        simp [h1, h2]

theorem σn_append_congr {n : ℕ} (hn : 2 ≤ n) {h h' : List Bool} (H : σn n h = σn n h')
    (z : List Bool) : σn n (h ++ z) = σn n (h' ++ z) := by
  induction z using List.reverseRecOn with
  | nil => simpa using H
  | append_singleton z e ih =>
    rw [← List.append_assoc, ← List.append_assoc, σn_snoc hn, σn_snoc hn, ih]

theorem σn_append_as {n : ℕ} (hn : 2 ≤ n) {w : List Bool} {f : Fin (n - 1) → Bool}
    (hw : σn n w = some f) (k : ℕ) :
    σn n (w ++ List.replicate k false) =
      some fun j => if hj : j.val < k then true else f ⟨j.val - k, by omega⟩ := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    rw [List.replicate_succ', ← List.append_assoc, σn_snoc hn, ih]
    simp only [σstep, Bool.false_eq_true, false_and, ↓reduceIte, Option.some.injEq]
    funext j
    by_cases hj : j.val = 0
    · simp [hj]
    · simp only [hj, ↓reduceDIte]
      by_cases hjk : j.val - 1 < k
      · simp [hjk, show j.val < k + 1 by omega]
      · simp only [hjk, ↓reduceDIte, show ¬ j.val < k + 1 by omega]
        congr 2
        omega

theorem Vn_distinguish {n : ℕ} (hn : 2 ≤ n) {w : List Bool} {f : Fin (n - 1) → Bool}
    (hw : σn n w = some f) (j : Fin (n - 1)) :
    Vn n (w ++ (List.replicate (n - 2 - j.val) false ++ [true])) = !(f j) := by
  rw [Vn_eq_isSome, ← List.append_assoc, σn_snoc hn, σn_append_as hn hw]
  simp only [σstep]
  have hfj : ∀ i : Fin (n - 1), i.val = n - 2 →
      ((if hi : i.val < n - 2 - j.val then true else f ⟨i.val - (n - 2 - j.val), by omega⟩) =
        f j) := by
    intro i hi
    simp only [show ¬ (i.val < n - 2 - j.val) by omega, ↓reduceDIte]
    congr 1
    ext
    simp only
    have := j.isLt
    omega
  split_ifs with hc
  · obtain ⟨-, i, hi, hfi⟩ := hc
    rw [hfj i hi] at hfi
    simp [hfi]
  · have hf : f j = false := by
      by_contra hf
      exact hc ⟨trivial, ⟨n - 2, by omega⟩, rfl, by rw [hfj _ rfl]; simpa using hf⟩
    simp [hf]

/-- Residual equivalence of `V_n` is exactly equality of residual states. -/
theorem σn_eq_iff_resEquiv {n : ℕ} (hn : 2 ≤ n) (h h' : List Bool) :
    σn n h = σn n h' ↔ ResEquiv (Vn n) h h' := by
  constructor
  · intro H z
    rw [Vn_eq_isSome, Vn_eq_isSome, σn_append_congr hn H]
  · intro H
    by_contra hne
    cases hh : σn n h with
    | none =>
      cases hh' : σn n h' with
      | none => exact hne (hh.trans hh'.symm)
      | some f' =>
        have := H []
        simp [Vn_eq_isSome, hh, hh'] at this
    | some f =>
      cases hh' : σn n h' with
      | none =>
        have := H []
        simp [Vn_eq_isSome, hh, hh'] at this
      | some f' =>
        have hff : f ≠ f' := fun hf => hne (by rw [hh, hh', hf])
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hff
        have := H (List.replicate (n - 2 - j.val) false ++ [true])
        rw [Vn_distinguish hn hh j, Vn_distinguish hn hh' j] at this
        exact hj (by simpa using this)

theorem σn_surjective {n : ℕ} (hn : 2 ≤ n) : Function.Surjective (σn n) := by
  intro o
  cases o with
  | none =>
    refine ⟨false :: List.replicate (n - 1) true, ?_⟩
    simp [σn, bad_a_bs hn]
  | some f =>
    refine ⟨List.ofFn fun i : Fin (n - 1) => !(f ⟨n - 2 - i.val, by omega⟩), ?_⟩
    have hnb : ¬ Bad n (List.ofFn fun i : Fin (n - 1) => !(f ⟨n - 2 - i.val, by omega⟩)) :=
      not_bad_of_length_lt (by simp; omega)
    simp only [σn, hnb, ↓reduceIte, Option.some.injEq, List.length_ofFn]
    funext j
    have hj := j.isLt
    rw [List.getElem?_ofFn]
    simp only [show n - 1 - 1 - j.val < n - 1 by omega, ↓reduceDIte]
    have hidx : (⟨n - 2 - (n - 1 - 1 - j.val), by omega⟩ : Fin (n - 1)) = j := by
      ext; simp only; omega
    simp only [hidx, hj, true_and, Option.some.injEq, Bool.not_eq_false']
    cases f j <;> simp

/-- Paper Thm 8.6(a): `ind(V_n) = 2^{n-1} + 1`. -/
theorem Vn_index {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (Quotient (resSetoid (Vn n))) = 2 ^ (n - 1) + 1 := by
  let Φ : Quotient (resSetoid (Vn n)) → Option (Fin (n - 1) → Bool) :=
    Quotient.lift (s := resSetoid (Vn n)) (σn n)
      (fun h h' H => (σn_eq_iff_resEquiv hn h h').mpr H)
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro a b hab
      induction a using Quotient.ind
      induction b using Quotient.ind
      exact Quotient.sound ((σn_eq_iff_resEquiv hn _ _).mp hab)
    · intro o
      obtain ⟨h, hh⟩ := σn_surjective hn o
      exact ⟨Quotient.mk _ h, hh⟩
  rw [Nat.card_eq_of_bijective Φ hΦ, Nat.card_eq_fintype_card, Fintype.card_option,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

end LikelyAllowed
