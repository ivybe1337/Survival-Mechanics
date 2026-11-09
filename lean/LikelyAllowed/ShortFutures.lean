/-
Copyright (c) 2026 Joshua Matthew Carter. Released under Apache 2.0 license.
Authors: Joshua Matthew Carter
-/
import LikelyAllowed.Predictive
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Paper Lemma 2.12: short continuations suffice (finite-dimensional processes)

If `p(x₁⋯xₙ) = α T^{x₁} ⋯ T^{xₙ} β` with `α, β ∈ ℝ^m`, then for `h, h' ∈ Supp(p)`,
`P_h = P_{h'}` iff `P_h(z) = P_{h'}(z)` for all `|z| ≤ m - 1` (Krylov-space argument).
-/

namespace LikelyAllowed

open Matrix Module

universe u

variable {α : Type u}

/-- The matrix product `T^{w} = T^{x₁} ⋯ T^{xₙ}` of a word. -/
def matWord {m : ℕ} (T : α → Matrix (Fin m) (Fin m) ℝ) (w : List α) :
    Matrix (Fin m) (Fin m) ℝ :=
  (w.map T).prod

section Krylov

variable {m : ℕ} (T : α → Matrix (Fin m) (Fin m) ℝ) (β : Fin m → ℝ)

@[simp] theorem matWord_nil : matWord T [] = 1 := rfl

theorem matWord_cons (x : α) (w : List α) : matWord T (x :: w) = T x * matWord T w := by
  simp [matWord]

theorem matWord_append (w z : List α) : matWord T (w ++ z) = matWord T w * matWord T z := by
  simp [matWord, List.prod_append]

/-- Generators `{T^z β : |z| ≤ j}`. -/
def krylovGen (j : ℕ) : Set (Fin m → ℝ) := {v | ∃ z : List α, z.length ≤ j ∧ v = matWord T z *ᵥ β}

/-- `W_j = span{T^z β : |z| ≤ j}`. -/
noncomputable def krylov (j : ℕ) : Submodule ℝ (Fin m → ℝ) := Submodule.span ℝ (krylovGen T β j)

theorem krylov_mono {i j : ℕ} (hij : i ≤ j) : krylov T β i ≤ krylov T β j :=
  Submodule.span_mono fun _ ⟨z, hz, hv⟩ => ⟨z, hz.trans hij, hv⟩

theorem mem_krylov_of_length {z : List α} {j : ℕ} (hz : z.length ≤ j) :
    matWord T z *ᵥ β ∈ krylov T β j :=
  Submodule.subset_span ⟨z, hz, rfl⟩

theorem mulVec_mem_krylov_succ (x : α) {j : ℕ} {v : Fin m → ℝ} (hv : v ∈ krylov T β j) :
    T x *ᵥ v ∈ krylov T β (j + 1) := by
  have hmap : Submodule.map (T x).mulVecLin (krylov T β j) ≤ krylov T β (j + 1) := by
    rw [krylov, Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨x :: z, by simp; omega, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, matWord_cons]
  exact hmap (Submodule.mem_map_of_mem hv)

/-- `W_{j+1} = W_j ⇒ W_{j+2} = W_{j+1}`. -/
theorem krylov_stable_succ {j : ℕ} (hst : krylov T β (j + 1) ≤ krylov T β j) :
    krylov T β (j + 2) ≤ krylov T β (j + 1) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨z, hz, rfl⟩
  cases z with
  | nil => exact mem_krylov_of_length T β (by simp)
  | cons x z =>
    rw [matWord_cons, ← Matrix.mulVec_mulVec]
    have hz' : z.length ≤ j + 1 := by simp at hz; omega
    exact mulVec_mem_krylov_succ T β x (hst (mem_krylov_of_length T β hz'))

theorem krylov_le_of_stable {i : ℕ} (hst : krylov T β (i + 1) ≤ krylov T β i) :
    ∀ j, krylov T β j ≤ krylov T β i := by
  have hall : ∀ j, i ≤ j → krylov T β (j + 1) ≤ krylov T β j := by
    intro j hij
    induction j, hij using Nat.le_induction with
    | base => exact hst
    | succ j _ ih => exact krylov_stable_succ T β ih
  intro j
  rcases le_total j i with h | h
  · exact krylov_mono T β h
  · induction j, h using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact (hall j hij).trans ih

/-- Every `T^z β` lies in `W_{m-1}` (the Krylov space stabilizes by step `m - 1`). -/
theorem mem_krylov_dim_sub_one (hβ : β ≠ 0) (z : List α) :
    matWord T z *ᵥ β ∈ krylov T β (m - 1) := by
  by_cases hex : ∃ i < m - 1, krylov T β (i + 1) ≤ krylov T β i
  · obtain ⟨i, hi, hst⟩ := hex
    exact krylov_mono T β hi.le
      (krylov_le_of_stable T β hst z.length (mem_krylov_of_length T β le_rfl))
  · push Not at hex
    have hgrow : ∀ j, j ≤ m - 1 → j + 1 ≤ finrank ℝ (krylov T β j) := by
      intro j hj
      induction j with
      | zero =>
        have hne : krylov T β 0 ≠ ⊥ := by
          intro hbot
          have hmem : β ∈ krylov T β 0 := by
            simpa using mem_krylov_of_length T β (z := ([] : List α)) (le_refl 0)
          rw [hbot, Submodule.mem_bot] at hmem
          exact hβ hmem
        have := Submodule.finrank_eq_zero.not.mpr hne
        omega
      | succ j ih =>
        have h1 := ih (by omega)
        have hlt : krylov T β j < krylov T β (j + 1) :=
          lt_of_le_of_ne (krylov_mono T β (Nat.le_succ j)) fun heq =>
            (hex j (by omega)) (le_of_eq heq.symm)
        have h2 := Submodule.finrank_lt_finrank_of_lt hlt
        omega
    have hle : finrank ℝ (krylov T β (m - 1)) ≤ m := by
      simpa using Submodule.finrank_le (krylov T β (m - 1))
    have htop : krylov T β (m - 1) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have := hgrow (m - 1) le_rfl
      simp only [finrank_fin_fun]
      omega
    rw [htop]
    exact Submodule.mem_top

/-- A vector annihilating the generators of `W_j` annihilates `W_j`. -/
theorem dotProduct_eq_zero_of_mem_krylov (u : Fin m → ℝ) {j : ℕ}
    (hu : ∀ z : List α, z.length ≤ j → u ⬝ᵥ (matWord T z *ᵥ β) = 0) {v : Fin m → ℝ}
    (hv : v ∈ krylov T β j) : u ⬝ᵥ v = 0 := by
  let K : Submodule ℝ (Fin m → ℝ) :=
    { carrier := {v | u ⬝ᵥ v = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [dotProduct_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [dotProduct_smul, ha, smul_zero] }
  have hle : krylov T β j ≤ K := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hu z hz
  exact hle hv

/-- Krylov form of Paper Lemma 2.12: if `u · T^z β = 0` for all `|z| ≤ m - 1` (and `β ≠ 0`) then
`u · T^z β = 0` for all `z`. -/
theorem dotProduct_eq_zero_of_short (hβ : β ≠ 0) (u : Fin m → ℝ)
    (hu : ∀ z : List α, z.length ≤ m - 1 → u ⬝ᵥ (matWord T z *ᵥ β) = 0) (z : List α) :
    u ⬝ᵥ (matWord T z *ᵥ β) = 0 :=
  dotProduct_eq_zero_of_mem_krylov T β u hu (mem_krylov_dim_sub_one T β hβ z)

end Krylov

variable [Fintype α]

/-- Paper Def 2.9: a linear representation of dimension `dim` of a process:
`p(x₁⋯xₙ) = init · T^{x₁} ⋯ T^{xₙ} · fin`. -/
structure LinRep (P : Process α) where
  /-- the dimension `m` -/
  dim : ℕ
  /-- the row vector `α` -/
  init : Fin dim → ℝ
  /-- the matrices `T^x` -/
  T : α → Matrix (Fin dim) (Fin dim) ℝ
  /-- the column vector `β` -/
  fin : Fin dim → ℝ
  rep : ∀ w, P.p w = init ⬝ᵥ (matWord T w *ᵥ fin)

namespace LinRep

variable {P : Process α} (L : LinRep P)

theorem fin_ne_zero : L.fin ≠ 0 := by
  intro h
  have := L.rep []
  rw [P.p_nil, h, Matrix.mulVec_zero, dotProduct_zero] at this
  exact one_ne_zero this

theorem pred_eq (h z : List α) :
    P.pred h z = (init L ᵥ* matWord L.T h) ⬝ᵥ (matWord L.T z *ᵥ L.fin) / P.p h := by
  unfold Process.pred
  rw [L.rep (h ++ z), matWord_append, ← Matrix.mulVec_mulVec, dotProduct_mulVec]

/-- Paper Lemma 2.12 (short continuations suffice). For `h, h' ∈ Supp(p)` and a linear
representation of dimension `m`: `h ~_ε h'` iff `P_h(z) = P_{h'}(z)` for all `|z| ≤ m - 1`. -/
theorem epsEquiv_iff_short {h h' : List α} (hh : P.p h ≠ 0) (hh' : P.p h' ≠ 0) :
    P.EpsEquiv h h' ↔ ∀ z : List α, z.length ≤ L.dim - 1 → P.pred h z = P.pred h' z := by
  constructor
  · intro H z _
    exact congrFun (P.pred_eq_of_epsEquiv H hh) z
  · intro H
    refine Or.inr ⟨hh, hh', fun z => ?_⟩
    set u : Fin L.dim → ℝ := (P.p h)⁻¹ • (init L ᵥ* matWord L.T h) -
      (P.p h')⁻¹ • (init L ᵥ* matWord L.T h')
    have key : ∀ y : List α, P.pred h y - P.pred h' y = u ⬝ᵥ (matWord L.T y *ᵥ L.fin) := by
      intro y
      rw [L.pred_eq, L.pred_eq, sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
        smul_eq_mul, div_eq_inv_mul, div_eq_inv_mul]
    have hz := dotProduct_eq_zero_of_short L.T L.fin L.fin_ne_zero u
      (fun y hy => by rw [← key, H y hy, sub_self]) z
    rw [← key, sub_eq_zero] at hz
    exact hz

end LinRep

end LikelyAllowed
