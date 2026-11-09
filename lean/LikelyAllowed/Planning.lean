/-
Copyright (c) 2026 Joshua Matthew Carter. Released under the MIT-0 license.
Authors: Joshua Matthew Carter
-/
import LikelyAllowed.Predictive
import LikelyAllowed.Conditioned
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Paper Proposition 6.3: planning with approximate residual states

Plans are infinite sequences `z : ℕ → α` (the paper's `z_t` is `z (t-1)`), `z_{≤t}` is
`pre z t`, `a_t(h,z) = V(h z_{≤t})`, and with rewards `r ∈ [0,1]` and `γ ∈ (0,1)`,
`G(h,z) = Σ_{t≥1} γ^{t-1} a_t(h,z) r(h z_{<t}, z_t)`, written here with `s = t - 1 ≥ 0`.
`W_Π(h) = sup_{z ∈ Pl} G(h,z)`.

The detection time `N_Π` enters through the hypothesis "the admissibility indicators agree for all
`t ≤ K` on all plans of `Pl`", i.e. `K ≤ N_Π - 1`; the bound is stated at `K`, which gives the
paper's bound at `K = N_Π - 1` (when `N_Π < ∞`) and for every `K` when `N_Π = ∞`.
-/

namespace LikelyAllowed

open Finset

universe u

variable {α : Type u}

/-- The length-`t` prefix `z_{≤t}` of a plan. -/
def pre (z : ℕ → α) (t : ℕ) : List α := List.ofFn fun i : Fin t => z i

@[simp] theorem pre_length (z : ℕ → α) (t : ℕ) : (pre z t).length = t := by simp [pre]

section Planning

variable (V : List α → Bool) (r : List α → α → ℝ) (γ : ℝ)

/-- The `s`-th discounted term `γ^s a_{s+1}(h,z) r(h z_{≤s}, z_{s})` (paper index `t = s + 1`). -/
noncomputable def planTerm (h : List α) (z : ℕ → α) (s : ℕ) : ℝ :=
  γ ^ s * bit (V (h ++ pre z (s + 1))) * r (h ++ pre z s) (z s)

/-- Paper §6.3: the discounted return `G(h,z)`. -/
noncomputable def planReturn (h : List α) (z : ℕ → α) : ℝ := ∑' s, planTerm V r γ h z s

/-- Paper §6.3: the value `W_Π(h) = sup_{z ∈ Pl} G(h,z)`. -/
noncomputable def planValue (Pl : Set (ℕ → α)) (h : List α) : ℝ :=
  sSup (planReturn V r γ h '' Pl)

variable {V r γ}

theorem planTerm_nonneg (hr0 : ∀ w e, 0 ≤ r w e) (hγ0 : 0 < γ) (h : List α) (z : ℕ → α)
    (s : ℕ) : 0 ≤ planTerm V r γ h z s := by
  unfold planTerm bit
  split_ifs
  · simpa using mul_nonneg (pow_nonneg hγ0.le s) (hr0 _ _)
  · simp

theorem planTerm_le (hr1 : ∀ w e, r w e ≤ 1) (hγ0 : 0 < γ) (h : List α) (z : ℕ → α)
    (s : ℕ) : planTerm V r γ h z s ≤ γ ^ s := by
  unfold planTerm bit
  split_ifs
  · simpa using mul_le_of_le_one_right (pow_nonneg hγ0.le s) (hr1 _ _)
  · simp [pow_nonneg hγ0.le s]

theorem planTerm_summable (hr0 : ∀ w e, 0 ≤ r w e) (hr1 : ∀ w e, r w e ≤ 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (h : List α) (z : ℕ → α) : Summable (planTerm V r γ h z) :=
  Summable.of_nonneg_of_le (planTerm_nonneg hr0 hγ0 h z) (planTerm_le hr1 hγ0 h z)
    (summable_geometric_of_lt_one hγ0.le hγ1)

theorem planReturn_nonneg (hr0 : ∀ w e, 0 ≤ r w e) (hγ0 : 0 < γ) (h : List α)
    (z : ℕ → α) : 0 ≤ planReturn V r γ h z :=
  tsum_nonneg (planTerm_nonneg hr0 hγ0 h z)

theorem planReturn_le (hr0 : ∀ w e, 0 ≤ r w e) (hr1 : ∀ w e, r w e ≤ 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (h : List α) (z : ℕ → α) : planReturn V r γ h z ≤ (1 - γ)⁻¹ := by
  rw [← tsum_geometric_of_lt_one hγ0.le hγ1]
  exact Summable.tsum_le_tsum (planTerm_le hr1 hγ0 h z)
    (planTerm_summable (V := V) hr0 hr1 hγ0 hγ1 h z) (summable_geometric_of_lt_one hγ0.le hγ1)

/-- `|sup f − sup g| ≤ sup |f − g|` over a nonempty family, for bounded-above functions. -/
theorem abs_sSup_image_sub_le {ι : Type*} {S : Set ι} (hS : S.Nonempty) {f g : ι → ℝ}
    (hf : BddAbove (f '' S)) (hg : BddAbove (g '' S)) {c : ℝ}
    (hc : ∀ i ∈ S, |f i - g i| ≤ c) : |sSup (f '' S) - sSup (g '' S)| ≤ c := by
  have h1 : sSup (f '' S) ≤ sSup (g '' S) + c := by
    refine csSup_le (hS.image f) ?_
    rintro _ ⟨i, hi, rfl⟩
    have := (abs_sub_le_iff.mp (hc i hi)).1
    have := le_csSup hg ⟨i, hi, rfl⟩
    linarith
  have h2 : sSup (g '' S) ≤ sSup (f '' S) + c := by
    refine csSup_le (hS.image g) ?_
    rintro _ ⟨i, hi, rfl⟩
    have := (abs_sub_le_iff.mp (hc i hi)).2
    have := le_csSup hf ⟨i, hi, rfl⟩
    linarith
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The bound `f(K+1) = Σ_{s<K} γ^s Δ_{s+1} + γ^K/(1-γ)` (paper's `f(T)` at `T = K + 1`). -/
noncomputable def planBound (γ : ℝ) (Δ : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ s ∈ range K, γ ^ s * Δ (s + 1) + γ ^ K * (1 - γ)⁻¹

/-- Paper Prop 6.3(a), per-plan layer: if the admissibility indicators agree up to step `K` along
`z`, and the step-`t` reward difference along `z` is at most `Δ_t`, then
`|G(h,z) − G(h',z)| ≤ Σ_{s<K} γ^s Δ_{s+1} + γ^K/(1-γ)`. -/
theorem abs_planReturn_sub_le (hr0 : ∀ w e, 0 ≤ r w e) (hr1 : ∀ w e, r w e ≤ 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {h h' : List α} (z : ℕ → α) (Δ : ℕ → ℝ) (K : ℕ)
    (hagree : ∀ t, t ≤ K → V (h ++ pre z t) = V (h' ++ pre z t))
    (hΔ : ∀ s, |r (h ++ pre z s) (z s) - r (h' ++ pre z s) (z s)| ≤ Δ (s + 1)) :
    |planReturn V r γ h z - planReturn V r γ h' z| ≤ planBound γ Δ K := by
  have hs1 := planTerm_summable (V := V) hr0 hr1 hγ0 hγ1 h z
  have hs2 := planTerm_summable (V := V) hr0 hr1 hγ0 hγ1 h' z
  have hgeo := summable_geometric_of_lt_one hγ0.le hγ1
  set d : ℕ → ℝ := fun s => planTerm V r γ h z s - planTerm V r γ h' z s
  set c : ℕ → ℝ := fun s => if s < K then γ ^ s * Δ (s + 1) else γ ^ s
  have hdc : ∀ s, |d s| ≤ c s := by
    intro s
    simp only [d, c]
    split_ifs with hs
    · unfold planTerm
      rw [hagree (s + 1) (by omega), ← mul_sub, abs_mul, abs_mul]
      have hb : |bit (V (h' ++ pre z (s + 1)))| ≤ 1 := by unfold bit; split_ifs <;> simp
      rw [abs_of_nonneg (pow_nonneg hγ0.le s)]
      calc γ ^ s * |bit (V (h' ++ pre z (s + 1)))| *
            |r (h ++ pre z s) (z s) - r (h' ++ pre z s) (z s)|
          ≤ γ ^ s * 1 * Δ (s + 1) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hb (pow_nonneg hγ0.le s)) (hΔ s)
              (abs_nonneg _) (by simpa using pow_nonneg hγ0.le s)
        _ = γ ^ s * Δ (s + 1) := by ring
    · rw [abs_sub_le_iff]
      have := planTerm_nonneg (V := V) hr0 hγ0 h z s
      have := planTerm_nonneg (V := V) hr0 hγ0 h' z s
      have := planTerm_le (V := V) hr1 hγ0 h z s
      have := planTerm_le (V := V) hr1 hγ0 h' z s
      constructor <;> linarith
  have hcs : Summable c := by
    rw [← summable_nat_add_iff K]
    refine (hgeo.mul_left (γ ^ K)).congr fun s => ?_
    simp only [c, show ¬ (s + K < K) by omega, ↓reduceIte, pow_add]
    ring
  have hds : Summable fun s => |d s| :=
    Summable.of_nonneg_of_le (fun s => abs_nonneg _) hdc hcs
  calc |planReturn V r γ h z - planReturn V r γ h' z|
      = |∑' s, d s| := by rw [planReturn, planReturn, ← hs1.tsum_sub hs2]
    _ ≤ ∑' s, |d s| := by
        have hd : Summable d := hs1.sub hs2
        rw [abs_le]
        constructor
        · rw [← tsum_neg]
          exact Summable.tsum_le_tsum (fun s => neg_abs_le (d s)) hds.neg hd
        · exact Summable.tsum_le_tsum (fun s => le_abs_self (d s)) hd hds
    _ ≤ ∑' s, c s := Summable.tsum_le_tsum hdc hds hcs
    _ = planBound γ Δ K := by
        rw [← hcs.sum_add_tsum_nat_add K, planBound]
        congr 1
        · exact Finset.sum_congr rfl fun s hs => by simp [c, mem_range.mp hs]
        · rw [← tsum_geometric_of_lt_one hγ0.le hγ1, ← tsum_mul_left]
          congr 1
          funext s
          simp only [c, show ¬ (s + K < K) by omega, ↓reduceIte, pow_add]
          ring

/-- Paper Prop 6.3(a). If on every plan in `Pl` the admissibility indicators of `h` and `h'`
agree up to step `K` (i.e. `K ≤ N_Π - 1`) and the step-`t` reward differences are at most
`Δ_t`, then `|W_Π(h) − W_Π(h')| ≤ Σ_{t ≤ K} γ^{t-1} Δ_t + γ^K/(1-γ)`. -/
theorem abs_planValue_sub_le (hr0 : ∀ w e, 0 ≤ r w e) (hr1 : ∀ w e, r w e ≤ 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {Pl : Set (ℕ → α)} (hPl : Pl.Nonempty) {h h' : List α}
    (Δ : ℕ → ℝ) (K : ℕ)
    (hagree : ∀ z ∈ Pl, ∀ t, t ≤ K → V (h ++ pre z t) = V (h' ++ pre z t))
    (hΔ : ∀ z ∈ Pl, ∀ s, |r (h ++ pre z s) (z s) - r (h' ++ pre z s) (z s)| ≤ Δ (s + 1)) :
    |planValue V r γ Pl h - planValue V r γ Pl h'| ≤ planBound γ Δ K := by
  have hbdd : ∀ g, BddAbove (planReturn V r γ g '' Pl) := fun g =>
    ⟨(1 - γ)⁻¹, by rintro _ ⟨z, -, rfl⟩; exact planReturn_le hr0 hr1 hγ0 hγ1 g z⟩
  exact abs_sSup_image_sub_le hPl (hbdd h) (hbdd h') fun z hz =>
    abs_planReturn_sub_le hr0 hr1 hγ0 hγ1 z Δ K (hagree z hz) (hΔ z hz)

/-- Paper Prop 6.3(c), abstract form: if rewards agree along all common continuations of `h`
and `h'` (e.g. `r` factors through `ε` and `ε(h) = ε(h')`), then
`|W_Π(h) − W_Π(h')| ≤ γ^K/(1-γ)` whenever admissibility agrees up to step `K`. -/
theorem abs_planValue_sub_le_of_reward_eq (hr0 : ∀ w e, 0 ≤ r w e) (hr1 : ∀ w e, r w e ≤ 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    {Pl : Set (ℕ → α)} (hPl : Pl.Nonempty)
    {h h' : List α} (K : ℕ)
    (hagree : ∀ z ∈ Pl, ∀ t, t ≤ K → V (h ++ pre z t) = V (h' ++ pre z t))
    (hrew : ∀ w e, r (h ++ w) e = r (h' ++ w) e) :
    |planValue V r γ Pl h - planValue V r γ Pl h'| ≤ γ ^ K * (1 - γ)⁻¹ := by
  have := abs_planValue_sub_le hr0 hr1 hγ0 hγ1 hPl (fun _ => 0) K hagree
    (fun z _ s => by rw [hrew, sub_self, abs_zero])
  simpa [planBound] using this

end Planning

/-- Paper Prop 6.3(b), `N_Π ≥ N_κ`: if no word of length `≤ K` separates the residuals of `h`
and `h'`, then no plan detects a difference up to step `K`. -/
theorem planAgree_of_resAgree {V : List α → Bool} {h h' : List α} {K : ℕ}
    (hres : ∀ w : List α, w.length ≤ K → V (h ++ w) = V (h' ++ w)) (z : ℕ → α) (t : ℕ)
    (ht : t ≤ K) : V (h ++ pre z t) = V (h' ++ pre z t) :=
  hres _ (by simpa using ht)

/-- Paper Prop 6.3(b), equality for `Pl = Σ^ℕ`: every separating word is detected by a plan. -/
theorem exists_plan_detect [Inhabited α] {V : List α → Bool} {h h' : List α} (w : List α)
    (hw : V (h ++ w) ≠ V (h' ++ w)) :
    ∃ z : ℕ → α, V (h ++ pre z w.length) ≠ V (h' ++ pre z w.length) := by
  refine ⟨fun i => w.getD i default, ?_⟩
  have hpre : pre (fun i => w.getD i default) w.length = w := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [pre, List.getD_eq_getElem?_getD]
  rwa [hpre]

/-- Paper Prop 6.3(c): if `r` factors through `ε` (`h ~_ε h' ⇒ r(h,·) = r(h',·)`) and
`ε(h) = ε(h')`, then `|W_Π(h) − W_Π(h')| ≤ γ^K/(1-γ)` whenever admissibility agrees up to step `K`.
With `K = N_Π - 1`, `γ^{N_Π - 1}/(1-γ) = γ^{N_Π}/(γ(1-γ))`. -/
theorem Process.abs_planValue_sub_le_of_eps [Fintype α] (P : Process α)
    {V : List α → Bool} {r : List α → α → ℝ} {γ : ℝ}
    (hr0 : ∀ w e, 0 ≤ r w e) (hr1 : ∀ w e, r w e ≤ 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hrε : ∀ g g' e, P.EpsEquiv g g' → r g e = r g' e)
    {Pl : Set (ℕ → α)} (hPl : Pl.Nonempty) {h h' : List α} (hε : P.EpsEquiv h h') (K : ℕ)
    (hagree : ∀ z ∈ Pl, ∀ t, t ≤ K → V (h ++ pre z t) = V (h' ++ pre z t)) :
    |planValue V r γ Pl h - planValue V r γ Pl h'| ≤ γ ^ K * (1 - γ)⁻¹ :=
  abs_planValue_sub_le_of_reward_eq hr0 hr1 hγ0 hγ1 hPl K hagree fun w e =>
    hrε _ _ e (P.epsEquiv_append hε w)

theorem pow_mul_inv_eq_div (γ : ℝ) (hγ : γ ≠ 0) (K : ℕ) :
    γ ^ K * (1 - γ)⁻¹ = γ ^ (K + 1) / (γ * (1 - γ)) := by
  rw [pow_succ, mul_comm γ (1 - γ), mul_div_mul_right _ _ hγ, div_eq_mul_inv]

/-! ### Paper Prop 6.3(d): tightness for the countdown family -/

/-- `V_N(w) = 1` iff `w` does not begin with `b` (`= true`) or `|w| ≤ N`. -/
def countdown (N : ℕ) (w : List Bool) : Bool := !(w.head? == some true) || decide (w.length ≤ N)

theorem countdown_resAgree (N : ℕ) (w : List Bool) (hw : w.length < N) :
    countdown N (false :: w) = countdown N (true :: w) := by
  simp [countdown]; omega

theorem countdown_separates (N : ℕ) :
    countdown N (false :: List.replicate N false) ≠
      countdown N (true :: List.replicate N false) := by
  simp [countdown]

variable {γ : ℝ}

theorem countdown_return_a (N : ℕ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (z : ℕ → Bool) :
    planReturn (countdown N) (fun _ _ => 1) γ [false] z = (1 - γ)⁻¹ := by
  rw [planReturn, ← tsum_geometric_of_lt_one hγ0.le hγ1]
  congr 1
  funext s
  simp [planTerm, countdown, bit]

theorem countdown_return_b (N : ℕ) (hN : 1 ≤ N) (hγ1 : γ < 1) (z : ℕ → Bool) :
    planReturn (countdown N) (fun _ _ => 1) γ [true] z = (1 - γ ^ (N - 1)) * (1 - γ)⁻¹ := by
  rw [planReturn, tsum_eq_sum (s := range (N - 1))]
  · have h1 : γ - 1 ≠ 0 := (by linarith : γ - 1 < 0).ne
    have h2 : 1 - γ ≠ 0 := (by linarith : (0 : ℝ) < 1 - γ).ne'
    have hg : ∑ i ∈ range (N - 1), γ ^ i = (1 - γ ^ (N - 1)) * (1 - γ)⁻¹ := by
      rw [geom_sum_eq (by linarith) (N - 1)]
      field_simp
      ring
    rw [← hg]
    refine Finset.sum_congr rfl fun s hs => ?_
    have : s + 1 ≤ N - 1 := mem_range.mp hs
    simp [planTerm, countdown, bit]; omega
  · intro s hs
    have : ¬ s < N - 1 := fun h => hs (mem_range.mpr h)
    simp [planTerm, countdown, bit]; omega

/-- Paper Prop 6.3(d): for the countdown semantics `V_N` with `r ≡ 1` and `Pl = Σ^ℕ`,
`N_κ(a, b) = N` (`countdown_resAgree`, `countdown_separates`) and
`W(a) − W(b) = γ^{N-1}/(1-γ)`, so the bound of (c) is attained. -/
theorem countdown_gap (N : ℕ) (hN : 1 ≤ N) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    planValue (countdown N) (fun _ _ => 1) γ Set.univ [false] -
      planValue (countdown N) (fun _ _ => 1) γ Set.univ [true] = γ ^ (N - 1) * (1 - γ)⁻¹ := by
  have hfa : planReturn (countdown N) (fun _ _ => 1) γ [false] = fun _ => (1 - γ)⁻¹ :=
    funext (countdown_return_a N hγ0 hγ1)
  have hfb : planReturn (countdown N) (fun _ _ => 1) γ [true] =
      fun _ => (1 - γ ^ (N - 1)) * (1 - γ)⁻¹ := funext (countdown_return_b N hN hγ1)
  simp only [planValue, hfa, hfb, Set.univ_nonempty.image_const, csSup_singleton]
  ring

end LikelyAllowed
