import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section

open BigOperators Finset

namespace DefectLadder

inductive Spin | up | down deriving DecidableEq, Repr

namespace Spin

def val : Spin → ℝ
  | up => 1
  | down => -1

instance : Fintype Spin where
  elems := {up, down}
  complete := by intro s; cases s <;> simp

lemma sum_spin (f : Spin → ℝ) : (∑ s : Spin, f s) = f Spin.up + f Spin.down := by
  have h : (Finset.univ : Finset Spin) = {Spin.up, Spin.down} := rfl
  rw [h, Finset.sum_insert]
  · rw [Finset.sum_singleton]
  · decide

end Spin

abbrev State := Spin × Spin

lemma sum_state (f : State → ℝ) :
    (∑ s : State, f s) =
    f (Spin.up, Spin.up) + f (Spin.up, Spin.down) +
    f (Spin.down, Spin.up) + f (Spin.down, Spin.down) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Spin.sum_spin]
  ring

/-!
===============================================================================
ВСПОМОГАТЕЛЬНЫЕ ЛЕММЫ ДЛЯ АЛГЕБРЫ ЭКСПОНЕНТ
===============================================================================
-/

lemma exp_add_eq (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y :=
  Real.exp_add x y

lemma exp_sub_eq (x y : ℝ) : Real.exp (x - y) = Real.exp x * Real.exp (-y) := by
  rw [sub_eq_add_neg, Real.exp_add]

/-!
===============================================================================
МАТРИЦА ПЕРЕНОСА НЕОДНОРОДНОГО ЗВЕНА И СПЕКТР
===============================================================================
-/

def transferMatrix (K_par K_perp : ℝ) (s t : State) : ℝ :=
  Real.exp (K_par * (s.1.val * t.1.val + s.2.val * t.2.val) +
            (1 / 2 : ℝ) * K_perp * (s.1.val * s.2.val + t.1.val * t.2.val))

def lambda2 (K_par K_perp : ℝ) : ℝ :=
  2 * Real.exp K_perp * Real.sinh (2 * K_par)

def lambda3 (K_par K_perp : ℝ) : ℝ :=
  2 * Real.exp (-K_perp) * Real.sinh (2 * K_par)

def lambda1 (K_par K_perp : ℝ) : ℝ :=
  2 * Real.cosh K_perp * Real.cosh (2 * K_par) +
  2 * Real.sqrt (Real.sinh K_perp ^ 2 * Real.cosh (2 * K_par) ^ 2 + 1)

/-- Вектор нечётной спин-флип моды: w₂ = (1, -1, 0, 0) -/
def eigenvec2 : State → ℝ
  | (Spin.up, Spin.up)     => 1
  | (Spin.down, Spin.down) => -1
  | _                      => 0

/-- Вектор нечётной моды перестановки рельсов: w₃ = (0, 0, 1, -1) -/
def eigenvec3 : State → ℝ
  | (Spin.up, Spin.down)   => 1
  | (Spin.down, Spin.up)   => -1
  | _                      => 0

/-!
===============================================================================
СОБСТВЕННЫЕ ЗНАЧЕНИЯ ОДНОГО ЗВЕНА
===============================================================================
-/

theorem eigenvec2_action (K_par K_perp : ℝ) (s : State) :
    (∑ t : State, transferMatrix K_par K_perp s t * eigenvec2 t) =
    lambda2 K_par K_perp * eigenvec2 s := by
  rw [sum_state]
  dsimp [eigenvec2]
  rcases s with ⟨s1, s2⟩
  cases s1 <;> cases s2
  · have h1 : K_par * (1 * 1 + 1 * 1) + 1 / 2 * K_perp * (1 * 1 + 1 * 1) = 2 * K_par + K_perp := by ring
    have h2 : K_par * (1 * -1 + 1 * -1) + 1 / 2 * K_perp * (1 * 1 + -1 * -1) = - (2 * K_par) + K_perp := by ring
    have e1 := exp_add_eq (2 * K_par) K_perp
    have e2 := exp_add_eq (- (2 * K_par)) K_perp
    dsimp [transferMatrix, Spin.val]
    rw [h1, h2, e1, e2]
    dsimp [lambda2]
    rw [Real.sinh_eq]
    ring
  · have h1 : K_par * (1 * 1 + -1 * 1) + 1 / 2 * K_perp * (1 * -1 + 1 * 1) = 0 := by ring
    have h2 : K_par * (1 * -1 + -1 * -1) + 1 / 2 * K_perp * (1 * -1 + -1 * -1) = 0 := by ring
    dsimp [transferMatrix, Spin.val]
    rw [h1, h2, Real.exp_zero]
    ring
  · have h1 : K_par * (-1 * 1 + 1 * 1) + 1 / 2 * K_perp * (-1 * 1 + 1 * 1) = 0 := by ring
    have h2 : K_par * (-1 * -1 + 1 * -1) + 1 / 2 * K_perp * (-1 * 1 + -1 * -1) = 0 := by ring
    dsimp [transferMatrix, Spin.val]
    rw [h1, h2, Real.exp_zero]
    ring
  · have h1 : K_par * (-1 * 1 + -1 * 1) + 1 / 2 * K_perp * (-1 * -1 + 1 * 1) = - (2 * K_par) + K_perp := by ring
    have h2 : K_par * (-1 * -1 + -1 * -1) + 1 / 2 * K_perp * (-1 * -1 + -1 * -1) = 2 * K_par + K_perp := by ring
    have e1 := exp_add_eq (- (2 * K_par)) K_perp
    have e2 := exp_add_eq (2 * K_par) K_perp
    dsimp [transferMatrix, Spin.val]
    rw [h1, h2, e1, e2]
    dsimp [lambda2]
    rw [Real.sinh_eq]
    ring

theorem eigenvec3_action (K_par K_perp : ℝ) (s : State) :
    (∑ t : State, transferMatrix K_par K_perp s t * eigenvec3 t) =
    lambda3 K_par K_perp * eigenvec3 s := by
  rw [sum_state]
  dsimp [eigenvec3]
  rcases s with ⟨s1, s2⟩
  cases s1 <;> cases s2
  · have h1 : K_par * (1 * 1 + 1 * -1) + 1 / 2 * K_perp * (1 * 1 + 1 * -1) = 0 := by ring
    have h2 : K_par * (1 * -1 + 1 * 1) + 1 / 2 * K_perp * (1 * 1 + -1 * 1) = 0 := by ring
    dsimp [transferMatrix, Spin.val]
    rw [h1, h2, Real.exp_zero]
    ring
  · have h1 : K_par * (1 * 1 + -1 * -1) + 1 / 2 * K_perp * (1 * -1 + 1 * -1) = 2 * K_par - K_perp := by ring
    have h2 : K_par * (1 * -1 + -1 * 1) + 1 / 2 * K_perp * (1 * -1 + -1 * 1) = - (2 * K_par) - K_perp := by ring
    have e1 := exp_sub_eq (2 * K_par) K_perp
    have e2 := exp_sub_eq (- (2 * K_par)) K_perp
    dsimp [transferMatrix, Spin.val]
    rw [h1, h2, e1, e2]
    dsimp [lambda3]
    rw [Real.sinh_eq]
    ring
  · have h1 : K_par * (-1 * 1 + 1 * -1) + 1 / 2 * K_perp * (-1 * 1 + 1 * -1) = - (2 * K_par) - K_perp := by ring
    have h2 : K_par * (-1 * -1 + 1 * 1) + 1 / 2 * K_perp * (-1 * 1 + -1 * 1) = 2 * K_par - K_perp := by ring
    have e1 := exp_sub_eq (- (2 * K_par)) K_perp
    have e2 := exp_sub_eq (2 * K_par) K_perp
    dsimp [transferMatrix, Spin.val]
    rw [h1, h2, e1, e2]
    dsimp [lambda3]
    rw [Real.sinh_eq]
    ring
  · have h1 : K_par * (-1 * 1 + -1 * -1) + 1 / 2 * K_perp * (-1 * -1 + 1 * -1) = 0 := by ring
    have h2 : K_par * (-1 * -1 + -1 * 1) + 1 / 2 * K_perp * (-1 * -1 + -1 * 1) = 0 := by ring
    dsimp [transferMatrix, Spin.val]
    rw [h1, h2, Real.exp_zero]
    ring

/-!
===============================================================================
ТЕОРЕМА: СОХРАНЕНИЕ И ФАКТОРИЗАЦИЯ СОБСТВЕННЫХ ЗНАЧЕНИЙ НЕОДНОРОДНОЙ ЦЕПОЧКИ
===============================================================================
-/

def matMul (A B : State → State → ℝ) (s t : State) : ℝ :=
  ∑ u : State, A s u * B u t

theorem defect_composite_eigenval2
    (K1_par K1_perp K2_par K2_perp : ℝ) (s : State) :
    (∑ t : State, matMul (transferMatrix K1_par K1_perp) (transferMatrix K2_par K2_perp) s t * eigenvec2 t) =
    (lambda2 K1_par K1_perp * lambda2 K2_par K2_perp) * eigenvec2 s := by
  dsimp [matMul]
  have h_swap :
      (∑ t : State, (∑ u : State, transferMatrix K1_par K1_perp s u * transferMatrix K2_par K2_perp u t) * eigenvec2 t) =
      ∑ u : State, transferMatrix K1_par K1_perp s u * (∑ t : State, transferMatrix K2_par K2_perp u t * eigenvec2 t) := by
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
  rw [h_swap]
  have h_inner (u : State) :
      (∑ t : State, transferMatrix K2_par K2_perp u t * eigenvec2 t) =
      lambda2 K2_par K2_perp * eigenvec2 u :=
    eigenvec2_action K2_par K2_perp u
  simp_rw [h_inner]
  have h_factor :
      (∑ u : State, transferMatrix K1_par K1_perp s u * (lambda2 K2_par K2_perp * eigenvec2 u)) =
      lambda2 K2_par K2_perp * (∑ u : State, transferMatrix K1_par K1_perp s u * eigenvec2 u) := by
    simp_rw [mul_left_comm (transferMatrix K1_par K1_perp s _)]
    rw [← Finset.mul_sum]
  rw [h_factor, eigenvec2_action]
  ring

theorem defect_composite_eigenval3
    (K1_par K1_perp K2_par K2_perp : ℝ) (s : State) :
    (∑ t : State, matMul (transferMatrix K1_par K1_perp) (transferMatrix K2_par K2_perp) s t * eigenvec3 t) =
    (lambda3 K1_par K1_perp * lambda3 K2_par K2_perp) * eigenvec3 s := by
  dsimp [matMul]
  have h_swap :
      (∑ t : State, (∑ u : State, transferMatrix K1_par K1_perp s u * transferMatrix K2_par K2_perp u t) * eigenvec3 t) =
      ∑ u : State, transferMatrix K1_par K1_perp s u * (∑ t : State, transferMatrix K2_par K2_perp u t * eigenvec3 t) := by
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
  rw [h_swap]
  have h_inner (u : State) :
      (∑ t : State, transferMatrix K2_par K2_perp u t * eigenvec3 t) =
      lambda3 K2_par K2_perp * eigenvec3 u :=
    eigenvec3_action K2_par K2_perp u
  simp_rw [h_inner]
  have h_factor :
      (∑ u : State, transferMatrix K1_par K1_perp s u * (lambda3 K2_par K2_perp * eigenvec3 u)) =
      lambda3 K2_par K2_perp * (∑ u : State, transferMatrix K1_par K1_perp s u * eigenvec3 u) := by
    simp_rw [mul_left_comm (transferMatrix K1_par K1_perp s _)]
    rw [← Finset.mul_sum]
  rw [h_factor, eigenvec3_action]
  ring

/-!
===============================================================================
ТЕОРЕМА: СТРОГОЕ ДОКАЗАТЕЛЬСТВО СПЕКТРАЛЬНОЙ ЩЕЛИ ДЛЯ ЛЮБЫХ K_|| > 0 И K_⊥
===============================================================================
-/

lemma cosh_gt_sinh (x : ℝ) : Real.sinh x < Real.cosh x := by
  have h : 0 < Real.exp (-x) := Real.exp_pos (-x)
  rw [Real.cosh_eq, Real.sinh_eq]
  linarith

lemma sqrt_sq_add_one_gt (u : ℝ) : u < Real.sqrt (u ^ 2 + 1) := by
  have h_pos : 0 < u ^ 2 + 1 := by positivity
  by_cases hu : 0 ≤ u
  · have h1 : u ^ 2 < u ^ 2 + 1 := by linarith
    have h2 := (Real.sqrt_lt_sqrt_iff (sq_nonneg u)).mpr h1
    rw [Real.sqrt_sq hu] at h2
    exact h2
  · have hu_neg : u < 0 := not_le.mp hu
    have h_sqrt_pos : 0 < Real.sqrt (u ^ 2 + 1) := Real.sqrt_pos.mpr h_pos
    exact hu_neg.trans h_sqrt_pos

lemma sqrt_sq_add_one_gt_neg (u : ℝ) : -u < Real.sqrt (u ^ 2 + 1) := by
  have h := sqrt_sq_add_one_gt (-u)
  rw [neg_sq] at h
  exact h

/--
**Фундаментальная теорема спектральной щели (Спин-флип):**
Для любых констант связи K_|| и K_⊥ ведущее собственное значение
λ₁ строго превосходит спин-флип значение λ₂:
  λ₁(K_||, K_⊥) > λ₂(K_||, K_⊥).
-/
theorem spectral_gap_spin_flip_pos
    (K_par K_perp : ℝ) :
    lambda2 K_par K_perp < lambda1 K_par K_perp := by
  dsimp [lambda1, lambda2]
  have h_sq : Real.sinh K_perp ^ 2 * Real.cosh (2 * K_par) ^ 2 =
              (Real.sinh K_perp * Real.cosh (2 * K_par)) ^ 2 := by
    rw [mul_pow]
  rw [h_sq]
  set u := Real.sinh K_perp * Real.cosh (2 * K_par)
  have h_sqrt := sqrt_sq_add_one_gt u
  have h_lead : 2 * Real.cosh K_perp * Real.cosh (2 * K_par) + 2 * u <
                2 * Real.cosh K_perp * Real.cosh (2 * K_par) +
                2 * Real.sqrt (u ^ 2 + 1) := by linarith
  have h_id : 2 * Real.cosh K_perp * Real.cosh (2 * K_par) + 2 * u =
              2 * Real.exp K_perp * Real.cosh (2 * K_par) := by
    dsimp [u]
    rw [Real.cosh_eq K_perp, Real.sinh_eq K_perp]
    ring
  rw [h_id] at h_lead
  have h_cs := cosh_gt_sinh (2 * K_par)
  have h_exp_pos : 0 < 2 * Real.exp K_perp := by positivity
  have h_cmp : 2 * Real.exp K_perp * Real.sinh (2 * K_par) <
               2 * Real.exp K_perp * Real.cosh (2 * K_par) :=
    mul_lt_mul_of_pos_left h_cs h_exp_pos
  exact h_cmp.trans h_lead

/--
**Фундаментальная теорема спектральной щели (Перестановка рельсов):**
Ведущее собственное значение λ₁ строго превосходит собственное значение λ₃:
  λ₁(K_||, K_⊥) > λ₃(K_||, K_⊥).
-/
theorem spectral_gap_rail_swap_pos
    (K_par K_perp : ℝ) :
    lambda3 K_par K_perp < lambda1 K_par K_perp := by
  dsimp [lambda1, lambda3]
  have h_sq : Real.sinh K_perp ^ 2 * Real.cosh (2 * K_par) ^ 2 =
              (Real.sinh K_perp * Real.cosh (2 * K_par)) ^ 2 := by
    rw [mul_pow]
  rw [h_sq]
  set u := Real.sinh K_perp * Real.cosh (2 * K_par)
  have h_sqrt := sqrt_sq_add_one_gt_neg u
  have h_lead : 2 * Real.cosh K_perp * Real.cosh (2 * K_par) + 2 * (-u) <
                2 * Real.cosh K_perp * Real.cosh (2 * K_par) +
                2 * Real.sqrt (u ^ 2 + 1) := by linarith
  have h_id : 2 * Real.cosh K_perp * Real.cosh (2 * K_par) + 2 * (-u) =
              2 * Real.exp (-K_perp) * Real.cosh (2 * K_par) := by
    dsimp [u]
    rw [Real.cosh_eq K_perp, Real.sinh_eq K_perp]
    ring
  rw [h_id] at h_lead
  have h_cs := cosh_gt_sinh (2 * K_par)
  have h_exp_pos : 0 < 2 * Real.exp (-K_perp) := by positivity
  have h_cmp : 2 * Real.exp (-K_perp) * Real.sinh (2 * K_par) <
               2 * Real.exp (-K_perp) * Real.cosh (2 * K_par) :=
    mul_lt_mul_of_pos_left h_cs h_exp_pos
  exact h_cmp.trans h_lead

end DefectLadder
