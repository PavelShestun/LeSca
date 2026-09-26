import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section

open BigOperators Finset

/-!
# LadderScaling.lean
Неасимптотический скейлинг анизотропной лестницы Изинга 2 x N.
Точное спектральное разложение трансфер-матрицы 4x4 через базис симметрии.
-/

namespace LadderIsing

inductive Spin | up | down deriving DecidableEq, Repr

namespace Spin

def val : Spin → ℝ
  | up => 1
  | down => -1

@[simp] lemma val_up : (up : Spin).val = 1 := rfl
@[simp] lemma val_down : (down : Spin).val = -1 := rfl

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
ВСПОМОГАТЕЛЬНЫЕ АЛГЕБРАИЧЕСКИЕ ЛЕММЫ ДЛЯ ЭКСПОНЕНТ
===============================================================================
-/

lemma exp_add_eq (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y :=
  Real.exp_add x y

lemma exp_sub_eq (x y : ℝ) : Real.exp (x - y) = Real.exp x * Real.exp (-y) := by
  rw [sub_eq_add_neg, Real.exp_add]

/-!
===============================================================================
МАТРИЦА ПЕРЕНОСА И АНАЛИТИЧЕСКИЙ СПЕКТР
===============================================================================
-/

/-- Элемент матрицы переноса 4x4 между слоями (s₁, s₂) и (t₁, t₂) -/
def ladderTransferMatrix (K_par K_perp : ℝ) (s t : State) : ℝ :=
  Real.exp (K_par * (s.1.val * t.1.val + s.2.val * t.2.val) +
            (1 / 2 : ℝ) * K_perp * (s.1.val * s.2.val + t.1.val * t.2.val))

/-- След матрицы переноса Tr(T) -/
def ladderTrace (K_par K_perp : ℝ) : ℝ :=
  ∑ s : State, ladderTransferMatrix K_par K_perp s s

/-- Четыре фундаментальных собственных значения -/
def lambda2 (K_par K_perp : ℝ) : ℝ :=
  2 * Real.exp K_perp * Real.sinh (2 * K_par)

def lambda3 (K_par K_perp : ℝ) : ℝ :=
  2 * Real.exp (-K_perp) * Real.sinh (2 * K_par)

def lambda1 (K_par K_perp : ℝ) : ℝ :=
  2 * Real.cosh K_perp * Real.cosh (2 * K_par) +
  2 * Real.sqrt (Real.sinh K_perp ^ 2 * Real.cosh (2 * K_par) ^ 2 + 1)

def lambda4 (K_par K_perp : ℝ) : ℝ :=
  2 * Real.cosh K_perp * Real.cosh (2 * K_par) -
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
ТЕОРЕМА 1: СОБСТВЕННАЯ СПИН-ФЛИП МОДА w₂ И ЗНАЧЕНИЕ λ₂
===============================================================================
-/

theorem ladder_eigenval_spin_flip (K_par K_perp : ℝ) (s : State) :
    (∑ t : State, ladderTransferMatrix K_par K_perp s t * eigenvec2 t) =
    lambda2 K_par K_perp * eigenvec2 s := by
  rw [sum_state]
  dsimp [eigenvec2]
  rcases s with ⟨s1, s2⟩
  cases s1 <;> cases s2
  · -- Case (up, up)
    have h1 : K_par * (1 * 1 + 1 * 1) + 1 / 2 * K_perp * (1 * 1 + 1 * 1) = 2 * K_par + K_perp := by ring
    have h2 : K_par * (1 * -1 + 1 * -1) + 1 / 2 * K_perp * (1 * 1 + -1 * -1) = - (2 * K_par) + K_perp := by ring
    have e1 := exp_add_eq (2 * K_par) K_perp
    have e2 := exp_add_eq (- (2 * K_par)) K_perp
    dsimp [ladderTransferMatrix, Spin.val]
    rw [h1, h2, e1, e2]
    dsimp [lambda2]
    rw [Real.sinh_eq]
    ring
  · -- Case (up, down)
    have h1 : K_par * (1 * 1 + -1 * 1) + 1 / 2 * K_perp * (1 * -1 + 1 * 1) = 0 := by ring
    have h2 : K_par * (1 * -1 + -1 * -1) + 1 / 2 * K_perp * (1 * -1 + -1 * -1) = 0 := by ring
    dsimp [ladderTransferMatrix, Spin.val]
    rw [h1, h2, Real.exp_zero]
    ring
  · -- Case (down, up)
    have h1 : K_par * (-1 * 1 + 1 * 1) + 1 / 2 * K_perp * (-1 * 1 + 1 * 1) = 0 := by ring
    have h2 : K_par * (-1 * -1 + 1 * -1) + 1 / 2 * K_perp * (-1 * 1 + -1 * -1) = 0 := by ring
    dsimp [ladderTransferMatrix, Spin.val]
    rw [h1, h2, Real.exp_zero]
    ring
  · -- Case (down, down)
    have h1 : K_par * (-1 * 1 + -1 * 1) + 1 / 2 * K_perp * (-1 * -1 + 1 * 1) = - (2 * K_par) + K_perp := by ring
    have h2 : K_par * (-1 * -1 + -1 * -1) + 1 / 2 * K_perp * (-1 * -1 + -1 * -1) = 2 * K_par + K_perp := by ring
    have e1 := exp_add_eq (- (2 * K_par)) K_perp
    have e2 := exp_add_eq (2 * K_par) K_perp
    dsimp [ladderTransferMatrix, Spin.val]
    rw [h1, h2, e1, e2]
    dsimp [lambda2]
    rw [Real.sinh_eq]
    ring

/-!
===============================================================================
ТЕОРЕМА 2: СОБСТВЕННАЯ МОДА ПЕРЕСТАНОВКИ РЕЛЬСОВ w₃ И ЗНАЧЕНИЕ λ₃
===============================================================================
-/

theorem ladder_eigenval_rail_swap (K_par K_perp : ℝ) (s : State) :
    (∑ t : State, ladderTransferMatrix K_par K_perp s t * eigenvec3 t) =
    lambda3 K_par K_perp * eigenvec3 s := by
  rw [sum_state]
  dsimp [eigenvec3]
  rcases s with ⟨s1, s2⟩
  cases s1 <;> cases s2
  · -- Case (up, up)
    have h1 : K_par * (1 * 1 + 1 * -1) + 1 / 2 * K_perp * (1 * 1 + 1 * -1) = 0 := by ring
    have h2 : K_par * (1 * -1 + 1 * 1) + 1 / 2 * K_perp * (1 * 1 + -1 * 1) = 0 := by ring
    dsimp [ladderTransferMatrix, Spin.val]
    rw [h1, h2, Real.exp_zero]
    ring
  · -- Case (up, down)
    have h1 : K_par * (1 * 1 + -1 * -1) + 1 / 2 * K_perp * (1 * -1 + 1 * -1) = 2 * K_par - K_perp := by ring
    have h2 : K_par * (1 * -1 + -1 * 1) + 1 / 2 * K_perp * (1 * -1 + -1 * 1) = - (2 * K_par) - K_perp := by ring
    have e1 := exp_sub_eq (2 * K_par) K_perp
    have e2 := exp_sub_eq (- (2 * K_par)) K_perp
    dsimp [ladderTransferMatrix, Spin.val]
    rw [h1, h2, e1, e2]
    dsimp [lambda3]
    rw [Real.sinh_eq]
    ring
  · -- Case (down, up)
    have h1 : K_par * (-1 * 1 + 1 * -1) + 1 / 2 * K_perp * (-1 * 1 + 1 * -1) = - (2 * K_par) - K_perp := by ring
    have h2 : K_par * (-1 * -1 + 1 * 1) + 1 / 2 * K_perp * (-1 * 1 + -1 * 1) = 2 * K_par - K_perp := by ring
    have e1 := exp_sub_eq (- (2 * K_par)) K_perp
    have e2 := exp_sub_eq (2 * K_par) K_perp
    dsimp [ladderTransferMatrix, Spin.val]
    rw [h1, h2, e1, e2]
    dsimp [lambda3]
    rw [Real.sinh_eq]
    ring
  · -- Case (down, down)
    have h1 : K_par * (-1 * 1 + -1 * -1) + 1 / 2 * K_perp * (-1 * -1 + 1 * -1) = 0 := by ring
    have h2 : K_par * (-1 * -1 + -1 * 1) + 1 / 2 * K_perp * (-1 * -1 + -1 * 1) = 0 := by ring
    dsimp [ladderTransferMatrix, Spin.val]
    rw [h1, h2, Real.exp_zero]
    ring

/-!
===============================================================================
ТЕОРЕМА 3: ТОЧНОЕ СОХРАНЕНИЕ СЛЕДА (Tr(T) = λ₁ + λ₂ + λ₃ + λ₄)
===============================================================================
-/

theorem ladder_trace_eq_sum_eigenvals (K_par K_perp : ℝ) :
    ladderTrace K_par K_perp =
    lambda1 K_par K_perp + lambda2 K_par K_perp +
    lambda3 K_par K_perp + lambda4 K_par K_perp := by
  dsimp [ladderTrace]
  rw [sum_state]
  dsimp [ladderTransferMatrix, Spin.val]
  have h1 : K_par * (1 * 1 + 1 * 1) + 1 / 2 * K_perp * (1 * 1 + 1 * 1) = 2 * K_par + K_perp := by ring
  have h2 : K_par * (1 * 1 + -1 * -1) + 1 / 2 * K_perp * (1 * -1 + 1 * -1) = 2 * K_par - K_perp := by ring
  have h3 : K_par * (-1 * -1 + 1 * 1) + 1 / 2 * K_perp * (-1 * 1 + -1 * 1) = 2 * K_par - K_perp := by ring
  have h4 : K_par * (-1 * -1 + -1 * -1) + 1 / 2 * K_perp * (-1 * -1 + -1 * -1) = 2 * K_par + K_perp := by ring
  rw [h1, h2, h3, h4]
  have e1 := exp_add_eq (2 * K_par) K_perp
  have e2 := exp_sub_eq (2 * K_par) K_perp
  rw [e1, e2]
  dsimp [lambda1, lambda2, lambda3, lambda4]
  rw [Real.cosh_eq K_perp, Real.cosh_eq (2 * K_par), Real.sinh_eq (2 * K_par)]
  ring

end LadderIsing
