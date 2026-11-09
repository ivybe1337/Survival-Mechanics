/-
Copyright (c) 2026 Joshua Matthew Carter. Released under the MIT-0 license.
Authors: Joshua Matthew Carter
-/
import LikelyAllowed.Predictive
import Mathlib.Data.Fintype.Vector

/-!
# §5 Survival-conditioned prediction: sufficiency of the joint state (Paper Prop 5.3)
-/

namespace LikelyAllowed

open Finset

universe u

variable {α : Type u} [Fintype α]

/-- `Σ^n`, the words of length `n`, as a `Finset`. -/
def words (α : Type u) [Fintype α] (n : ℕ) : Finset (List α) :=
  (Finset.univ : Finset (List.Vector α n)).map
    ⟨fun v => v.toList, fun _ _ h => List.Vector.toList_injective h⟩

theorem mem_words {n : ℕ} {w : List α} : w ∈ words α n ↔ w.length = n := by
  constructor
  · intro hw
    obtain ⟨v, -, rfl⟩ := Finset.mem_map.mp hw
    exact v.toList_length
  · intro hw
    exact Finset.mem_map.mpr ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩

/-- `{0,1}`-valued indicator of a Boolean, as a real number. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

namespace Process

variable (P : Process α) (V : List α → Bool)

/-- Paper Prop 5.3 (sufficiency), general finite form: for a finite set `Z` of
continuations and any `g`, the sum `Σ_{z∈Z} P_h(z) g(V_h, z)` depends only on `J(h)` (for `h ∈ Supp
p`). Here the residual `R_V(h)` is represented by the residual function `V_h : z ↦ V(hz)`.
-/
theorem sum_pred_mul_eq_of_jEquiv (Z : Finset (List α))
    (g : (List α → Bool) → List α → ℝ) {h h' : List α} (hJ : P.JEquiv V h h')
    (hh : P.p h ≠ 0) :
    ∑ z ∈ Z, (P.p (h ++ z) / P.p h) * g (residual V h) z =
      ∑ z ∈ Z, (P.p (h' ++ z) / P.p h') * g (residual V h') z := by
  have e1 := P.pred_eq_of_epsEquiv hJ.1 hh
  have e2 := resEquiv_iff_residual_eq.mp hJ.2
  rw [e2]
  refine Finset.sum_congr rfl fun z _ => ?_
  have e3 := congrFun e1 z
  unfold pred at e3
  rw [e3]

/-- Paper Prop 5.3, with `g` taking the residual set `R_V(h) = {z | V(hz) = 1}`
literally. -/
theorem sum_pred_mul_resSet_eq_of_jEquiv (Z : Finset (List α))
    (g : Set (List α) → List α → ℝ) {h h' : List α} (hJ : P.JEquiv V h h')
    (hh : P.p h ≠ 0) :
    ∑ z ∈ Z, (P.p (h ++ z) / P.p h) * g (resSet V h) z =
      ∑ z ∈ Z, (P.p (h' ++ z) / P.p h') * g (resSet V h') z :=
  P.sum_pred_mul_eq_of_jEquiv V Z (fun R z => g {y | R y = true} z) hJ hh

/-- Paper §5. The `n`-step survival probability `S_n(h) = Σ_{z∈Σ^n} P_h(z) V(hz)`. -/
noncomputable def survProb (n : ℕ) (h : List α) : ℝ :=
  ∑ z ∈ words α n, P.pred h z * bit (V (h ++ z))

/-- Paper §5. The conditioned law `Q_n(z|h) = P_h(z) V(hz) / S_n(h)` (for `z ∈ Σ^n`). -/
noncomputable def condLaw (n : ℕ) (h z : List α) : ℝ :=
  P.pred h z * bit (V (h ++ z)) / P.survProb V n h

/-- Paper Prop 5.3 (consequence): `S_n` depends only on `J(h)`. -/
theorem survProb_eq_of_jEquiv (n : ℕ) {h h' : List α} (hJ : P.JEquiv V h h')
    (hh : P.p h ≠ 0) : P.survProb V n h = P.survProb V n h' :=
  P.sum_pred_mul_eq_of_jEquiv V (words α n) (fun R z => bit (R z)) hJ hh

/-- Paper Prop 5.3 (consequence): `Q_n(·|h)` depends only on `J(h)`. -/
theorem condLaw_eq_of_jEquiv (n : ℕ) {h h' : List α} (hJ : P.JEquiv V h h')
    (hh : P.p h ≠ 0) (z : List α) : P.condLaw V n h z = P.condLaw V n h' z := by
  unfold condLaw
  rw [P.survProb_eq_of_jEquiv V n hJ hh, P.pred_eq_of_epsEquiv hJ.1 hh, hJ.2 z]

/-- Paper Prop 5.3 (consequence, `n = ∞`), for any limit functional `lim` (e.g. the
limit, or the infimum, of the nonincreasing sequence `(S_n(h))_n`): `S_∞(h) := lim_n S_n(h)`. -/
noncomputable def survInf (lim : (ℕ → ℝ) → ℝ) (h : List α) : ℝ :=
  lim fun n => P.survProb V n h

/-- Paper §5. `Q_∞(z|h) = P_h(z) S_∞(hz) / S_∞(h)`. -/
noncomputable def condLawInf (lim : (ℕ → ℝ) → ℝ) (h z : List α) : ℝ :=
  P.pred h z * P.survInf V lim (h ++ z) / P.survInf V lim h

theorem survInf_eq_of_jEquiv (lim : (ℕ → ℝ) → ℝ) {h h' : List α} (hJ : P.JEquiv V h h')
    (hh : P.p h ≠ 0) : P.survInf V lim h = P.survInf V lim h' := by
  unfold survInf
  congr 1
  funext n
  exact P.survProb_eq_of_jEquiv V n hJ hh

/-- Paper Prop 5.3 (consequence, `n = ∞`): `Q_∞(·|h)` depends only on `J(h)`. If
`P_h(z) = 0` the term vanishes; otherwise `J(hz)` is determined by `J(h)` and `z` by right
congruence. -/
theorem condLawInf_eq_of_jEquiv (lim : (ℕ → ℝ) → ℝ) {h h' : List α}
    (hJ : P.JEquiv V h h') (hh : P.p h ≠ 0) (z : List α) :
    P.condLawInf V lim h z = P.condLawInf V lim h' z := by
  unfold condLawInf
  have hpred := congrFun (P.pred_eq_of_epsEquiv hJ.1 hh) z
  rw [P.survInf_eq_of_jEquiv V lim hJ hh, ← hpred]
  by_cases hz : P.p (h ++ z) = 0
  · simp [pred, hz]
  · rw [P.survInf_eq_of_jEquiv V lim ((P.jEquiv_rightCongr V).append hJ z) hz]

end Process

end LikelyAllowed
