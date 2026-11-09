/-
Copyright (c) 2026 Joshua Matthew Carter. Released under the MIT-0 license.
Authors: Joshua Matthew Carter
-/
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Combinatorics.SetFamily.Shatter

/-!
# §7 Certificates (Paper Lemma 7.1, Prop 7.3, Lemma 7.4, Prop 7.5)

Finite universe `L = β` with `n = |β|`; `K ⊆ 2^L` nonempty and down-closed; `M` the minimal
non-members of `K`.
-/

namespace LikelyAllowed

open Finset

universe u

variable {β : Type u} [Fintype β] [DecidableEq β]

/-- `K` is down-closed (a simplicial complex, possibly `∅`). -/
def DownClosed (K : Finset (Finset β)) : Prop := ∀ σ ∈ K, ∀ τ ⊆ σ, τ ∈ K

/-- Paper §7. The minimal non-members `M` of `K`: `m ∉ K` and every proper subset of `m` is
in `K`. -/
def minNonMembers (K : Finset (Finset β)) : Finset (Finset β) :=
  univ.filter fun m => m ∉ K ∧ ∀ τ ∈ m.ssubsets, τ ∈ K

theorem mem_minNonMembers {K : Finset (Finset β)} {m : Finset β} :
    m ∈ minNonMembers K ↔ m ∉ K ∧ ∀ τ, τ ⊂ m → τ ∈ K := by
  simp [minNonMembers, mem_ssubsets]

/-- Paper §7. The minimal non-members form an antichain. -/
theorem minNonMembers_isAntichain (K : Finset (Finset β)) :
    IsAntichain (· ⊆ ·) (SetLike.coe (minNonMembers K)) := by
  intro a ha b hb hab hsub
  have ha' := mem_minNonMembers.mp ha
  have hb' := mem_minNonMembers.mp hb
  exact ha'.1 (hb'.2 a (ssubset_of_subset_of_ne hsub hab))

/-- Every non-member contains a minimal non-member. -/
theorem exists_minNonMember_subset (K : Finset (Finset β)) (σ : Finset β) (hσ : σ ∉ K) :
    ∃ m ∈ minNonMembers K, m ⊆ σ := by
  induction σ using Finset.strongInduction with
  | H σ ih =>
    by_cases hall : ∀ τ, τ ⊂ σ → τ ∈ K
    · exact ⟨σ, mem_minNonMembers.mpr ⟨hσ, hall⟩, subset_refl _⟩
    · push Not at hall
      obtain ⟨τ, hτ, hτK⟩ := hall
      obtain ⟨m, hm, hmτ⟩ := ih τ hτ hτK
      exact ⟨m, hm, hmτ.trans hτ.subset⟩

/-- Paper Lemma 7.1 (T9, reconstruction). For down-closed `K`,
`K = {σ | no m ∈ M with m ⊆ σ}`. -/
theorem mem_iff_no_minNonMember_subset {K : Finset (Finset β)} (hK : DownClosed K)
    (σ : Finset β) : σ ∈ K ↔ ∀ m ∈ minNonMembers K, ¬ m ⊆ σ := by
  constructor
  · intro hσ m hm hmσ
    exact (mem_minNonMembers.mp hm).1 (hK σ hσ m hmσ)
  · intro H
    by_contra hσ
    obtain ⟨m, hm, hmσ⟩ := exists_minNonMember_subset K σ hσ
    exact H m hm hmσ

/-- Paper Prop 7.3 (T14), bound: `|M| ≤ C(n, ⌊n/2⌋)` (Sperner). -/
theorem card_minNonMembers_le_sperner (K : Finset (Finset β)) :
    #(minNonMembers K) ≤ (Fintype.card β).choose (Fintype.card β / 2) :=
  (minNonMembers_isAntichain K).sperner

omit [Fintype β] in
/-- Paper Lemma 7.4. A down-closed `K` shatters `S` iff `S ∈ K`. -/
theorem shatters_iff_mem {K : Finset (Finset β)} (hK : DownClosed K) (S : Finset β) :
    K.Shatters S ↔ S ∈ K := by
  constructor
  · intro hS
    obtain ⟨u, hu, hSu⟩ := hS (subset_refl S)
    exact hK u hu S (by rw [← hSu]; exact inter_subset_right)
  · intro hS t ht
    exact ⟨t, hK S hS t ht, inter_eq_right.mpr ht⟩

omit [Fintype β] [DecidableEq β] in
theorem DownClosed.isLowerSet {K : Finset (Finset β)} (hK : DownClosed K) :
    IsLowerSet (SetLike.coe K) :=
  fun a b hba ha => hK a ha b hba

omit [Fintype β] in
/-- Paper Lemma 7.4. For down-closed `K`, `VC(K) = dim(K) := max{|σ| : σ ∈ K}`. -/
theorem vcDim_eq_dim {K : Finset (Finset β)} (hK : DownClosed K) :
    K.vcDim = K.sup card := by
  unfold vcDim
  rw [shatterer_eq.mpr hK.isLowerSet]

/-- `choose n` is monotone on `[0, n/2]`. -/
theorem choose_le_choose_of_le_half {n i j : ℕ} (hij : i ≤ j) (hj : j ≤ n / 2) :
    n.choose i ≤ n.choose j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- Binomial unimodality: `i ≤ k ⇒ C(n,i) ≤ C(n, min(k, ⌊n/2⌋))`. -/
theorem choose_le_choose_min_half {n i k : ℕ} (hik : i ≤ k) :
    n.choose i ≤ n.choose (min k (n / 2)) := by
  rcases le_total k (n / 2) with h | h
  · rw [min_eq_left h]; exact choose_le_choose_of_le_half hik h
  · rw [min_eq_right h]; exact Nat.choose_le_middle i n

omit [DecidableEq β] in
/-- LYM consequence: an antichain of sets of size `≤ k` has at most `C(n, min(k, ⌊n/2⌋))`
members. -/
theorem IsAntichain.card_le_choose_min {A : Finset (Finset β)}
    (hA : IsAntichain (· ⊆ ·) (SetLike.coe A)) {k : ℕ} (hk : ∀ a ∈ A, #a ≤ k) :
    #A ≤ (Fintype.card β).choose (min k (Fintype.card β / 2)) := by
  set n := Fintype.card β
  set C := n.choose (min k (n / 2))
  have hCpos : (0 : ℚ) < C :=
    Nat.cast_pos.mpr (Nat.choose_pos ((min_le_right _ _).trans (Nat.div_le_self _ _)))
  have h : ∑ _s ∈ A, (C : ℚ)⁻¹ ≤ 1 := by
    calc ∑ _s ∈ A, (C : ℚ)⁻¹ ≤ ∑ s ∈ A, (n.choose #s : ℚ)⁻¹ := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hpos : (0 : ℚ) < n.choose #s := Nat.cast_pos.mpr (Nat.choose_pos s.card_le_univ)
          exact inv_anti₀ hpos (by exact_mod_cast choose_le_choose_min_half (hk s hs))
      _ ≤ 1 := lubell_yamamoto_meshalkin_inequality_sum_inv_choose hA
  rw [Finset.sum_const, nsmul_eq_mul, mul_inv_le_iff₀ hCpos, one_mul] at h
  exact_mod_cast h

section Complex
variable {K : Finset (Finset β)}

omit [Fintype β] [DecidableEq β] in
theorem empty_mem_of_downClosed (hK : DownClosed K) (hne : K.Nonempty) : (∅ : Finset β) ∈ K := by
  obtain ⟨σ, hσ⟩ := hne
  exact hK σ hσ ∅ (empty_subset σ)

/-- Paper Prop 7.5 (U2), first part: every minimal non-member has `|m| ≤ dim(K) +
1`. -/
theorem card_le_dim_succ_of_mem_minNonMembers (hK : DownClosed K) (hne : K.Nonempty)
    {m : Finset β} (hm : m ∈ minNonMembers K) : #m ≤ K.sup card + 1 := by
  have hm' := mem_minNonMembers.mp hm
  have hmne : m.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    exact hm'.1 (empty_mem_of_downClosed hK hne)
  obtain ⟨x, hx⟩ := hmne
  have hmem : m.erase x ∈ K := hm'.2 _ (erase_ssubset hx)
  have h1 : #(m.erase x) ≤ K.sup card := le_sup (f := card) hmem
  have h2 := card_erase_add_one hx
  omega

/-- Paper Prop 7.5 (U2), second part: `|M| ≤ C(n, min(d+1, ⌊n/2⌋))` with `d =
dim(K)`. -/
theorem card_minNonMembers_le (hK : DownClosed K) (hne : K.Nonempty) :
    #(minNonMembers K) ≤
      (Fintype.card β).choose (min (K.sup card + 1) (Fintype.card β / 2)) :=
  IsAntichain.card_le_choose_min (minNonMembers_isAntichain K)
    fun _ hm => card_le_dim_succ_of_mem_minNonMembers hK hne hm

/-- Paper Prop 7.5, stated over the class `dim(K) ≤ d`: `|M| ≤ C(n, min(d+1,
⌊n/2⌋))`. Together with `dim_bound_tight` this is the exact maximum (for `n ≥ 2`). -/
theorem card_minNonMembers_le_of_dim_le (hK : DownClosed K) (hne : K.Nonempty) {d : ℕ}
    (hd : K.sup card ≤ d) :
    #(minNonMembers K) ≤ (Fintype.card β).choose (min (d + 1) (Fintype.card β / 2)) :=
  IsAntichain.card_le_choose_min (minNonMembers_isAntichain K)
    fun _ hm => (card_le_dim_succ_of_mem_minNonMembers hK hne hm).trans (by omega)

omit [DecidableEq β] in
/-- Paper Prop 7.5 (Sauer–Shelah): `|K| ≤ Σ_{i ≤ d} C(n, i)`. -/
theorem card_le_sum_choose (hK : DownClosed K) :
    #K ≤ ∑ i ∈ Iic (K.sup card), (Fintype.card β).choose i := by
  classical
  have h := card_shatterer_le_sum_vcDim (𝒜 := K)
  rwa [shatterer_eq.mpr hK.isLowerSet, vcDim_eq_dim hK] at h

end Complex

/-! ### Tightness: threshold complexes -/

/-- The threshold complex `K_t = {σ : |σ| < t}` (all sets of size at most `t - 1`). -/
def threshold (β : Type u) [Fintype β] [DecidableEq β] (t : ℕ) : Finset (Finset β) :=
  univ.filter fun σ => #σ < t

theorem threshold_downClosed (t : ℕ) : DownClosed (threshold β t) := by
  intro σ hσ τ hτ
  simp only [threshold, mem_filter, mem_univ, true_and] at hσ ⊢
  exact (card_le_card hτ).trans_lt hσ

/-- The minimal non-members of the threshold complex `K_t` are exactly the `t`-sets. -/
theorem minNonMembers_threshold (t : ℕ) :
    minNonMembers (threshold β t) = powersetCard t univ := by
  ext m
  rw [mem_minNonMembers, mem_powersetCard_univ]
  simp only [threshold, mem_filter, mem_univ, true_and, not_lt]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hne
    have hlt : t < #m := lt_of_le_of_ne h1 (Ne.symm hne)
    have hmne : m.Nonempty := card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hmne
    have := h2 _ (erase_ssubset hx)
    have h3 := card_erase_add_one hx
    omega
  · intro h
    exact ⟨h.ge, fun τ hτ => h ▸ card_lt_card hτ⟩

theorem card_minNonMembers_threshold (t : ℕ) :
    #(minNonMembers (threshold β t)) = (Fintype.card β).choose t := by
  rw [minNonMembers_threshold, card_powersetCard, card_univ]

theorem sup_card_threshold_le (t : ℕ) : (threshold β t).sup card ≤ t - 1 := by
  refine Finset.sup_le fun σ hσ => ?_
  simp only [threshold, mem_filter, mem_univ, true_and] at hσ
  omega

theorem threshold_nonempty {t : ℕ} (ht : 1 ≤ t) : (threshold β t).Nonempty :=
  ⟨∅, by simp [threshold]; omega⟩

/-- Paper Prop 7.3, tightness: for `n ≥ 2`, `K = {σ : |σ| ≤ ⌊n/2⌋ - 1}` is a nonempty
down-closed family with `|M| = C(n, ⌊n/2⌋)`. -/
theorem sperner_tight (hn : 2 ≤ Fintype.card β) :
    DownClosed (threshold β (Fintype.card β / 2)) ∧ (threshold β (Fintype.card β / 2)).Nonempty ∧
      #(minNonMembers (threshold β (Fintype.card β / 2))) =
        (Fintype.card β).choose (Fintype.card β / 2) :=
  ⟨threshold_downClosed _, threshold_nonempty (by omega), card_minNonMembers_threshold _⟩

/-- Paper Prop 7.5, tightness (for `n ≥ 2`): for every `d`, there is a nonempty
down-closed `K` with `dim(K) ≤ d` and `|M| = C(n, min(d+1, ⌊n/2⌋))`. -/
theorem dim_bound_tight (hn : 2 ≤ Fintype.card β) (d : ℕ) :
    ∃ K : Finset (Finset β), DownClosed K ∧ K.Nonempty ∧ K.sup card ≤ d ∧
      #(minNonMembers K) = (Fintype.card β).choose (min (d + 1) (Fintype.card β / 2)) := by
  refine ⟨threshold β (min (d + 1) (Fintype.card β / 2)), threshold_downClosed _,
    threshold_nonempty ?_, ?_, card_minNonMembers_threshold _⟩
  · have : 1 ≤ Fintype.card β / 2 := by omega
    omega
  · exact (sup_card_threshold_le _).trans (by omega)

/-- Paper Prop 7.3, tightness for every `n ≥ 1`: some nonempty down-closed `K` has
`|M(K)| = C(n, ⌊n/2⌋)` (for `n = 1` take `K = {∅}`). -/
theorem sperner_tight_of_pos (hn : 1 ≤ Fintype.card β) :
    ∃ K : Finset (Finset β), DownClosed K ∧ K.Nonempty ∧
      #(minNonMembers K) = (Fintype.card β).choose (Fintype.card β / 2) := by
  by_cases h2 : 2 ≤ Fintype.card β
  · exact ⟨_, sperner_tight h2⟩
  · have h1 : Fintype.card β = 1 := by omega
    refine ⟨threshold β 1, threshold_downClosed 1, threshold_nonempty le_rfl, ?_⟩
    rw [card_minNonMembers_threshold, h1]
    rfl

/-- Paper Prop 7.5, exactness for every `n ≥ 1`: for every `r` there is a nonempty down-closed
`K` of rank `≤ r` with `|M(K)| = C(n, min(r+1, ⌊n/2⌋))`. -/
theorem dim_bound_tight_of_pos (hn : 1 ≤ Fintype.card β) (d : ℕ) :
    ∃ K : Finset (Finset β), DownClosed K ∧ K.Nonempty ∧ K.sup card ≤ d ∧
      #(minNonMembers K) = (Fintype.card β).choose (min (d + 1) (Fintype.card β / 2)) := by
  by_cases h2 : 2 ≤ Fintype.card β
  · exact dim_bound_tight h2 d
  · have h1 : Fintype.card β = 1 := by omega
    refine ⟨threshold β 1, threshold_downClosed 1, threshold_nonempty le_rfl,
      (sup_card_threshold_le 1).trans (by omega), ?_⟩
    rw [card_minNonMembers_threshold, h1]
    simp

end LikelyAllowed
