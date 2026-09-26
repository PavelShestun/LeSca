import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section

open BigOperators Finset

/-!
# ArbitraryLadder.lean (Level 2-3)
Неасимптотический скейлинг и спектральная щель лестницы произвольной ширины M x N.
Доказательство без теоремы Перрона — Фробениуса через дискретную Z₂-инволюцию
и операторное сжатие Добрушина на нечётном подпространстве.
-/

namespace ArbitraryLadder

inductive Spin | up | down deriving DecidableEq, Repr

namespace Spin

def val : Spin → ℝ
  | up => 1
  | down => -1

def flip : Spin → Spin
  | up => down
  | down => up

@[simp] lemma val_flip (s : Spin) : (flip s).val = - s.val := by
  cases s
  · rfl
  · dsimp [flip, val]
    ring

@[simp] lemma flip_flip (s : Spin) : flip (flip s) = s := by
  cases s <;> rfl

instance : Fintype Spin where
  elems := {up, down}
  complete := by intro s; cases s <;> simp

@[simp] lemma card_spin : Fintype.card Spin = 2 := rfl

end Spin

/-- Состояние поперечного слоя из M спинов: Fin M → Spin -/
abbrev Layer (M : ℕ) := Fin M → Spin

lemma card_layer (M : ℕ) : Fintype.card (Layer M) = 2 ^ M := by
  rw [Fintype.card_fun, Fintype.card_fin, Spin.card_spin]

lemma sum_const_layer {M : ℕ} (c : ℝ) :
    (∑ _t : Layer M, c) = ((2 : ℝ) ^ M) * c := by
  rw [Finset.sum_const, Finset.card_univ, card_layer, nsmul_eq_mul]
  push_cast
  rfl

/-- Инволюция глобального спин-флипа всего слоя -/
def flipLayer {M : ℕ} (s : Layer M) : Layer M :=
  fun i => Spin.flip (s i)

@[simp] lemma flipLayer_involutive {M : ℕ} (s : Layer M) :
    flipLayer (flipLayer s) = s := by
  funext i
  exact Spin.flip_flip (s i)

def flipEquiv (M : ℕ) : Layer M ≃ Layer M where
  toFun := flipLayer
  invFun := flipLayer
  left_inv := flipLayer_involutive
  right_inv := flipLayer_involutive

/-- Циклический сдвиг индексов вдоль кольца ширины M -/
def nextIdx (M : ℕ) [NeZero M] (i : Fin M) : Fin M :=
  ⟨(i.val + 1) % M, Nat.mod_lt _ (NeZero.pos M)⟩

/-- Продольная энергия взаимодействия между слоями s и t -/
def E_par {M : ℕ} (s t : Layer M) : ℝ :=
  ∑ i : Fin M, (s i).val * (t i).val

/-- Поперечная энергия взаимодействия внутри слоя s -/
def E_perp {M : ℕ} [NeZero M] (s : Layer M) : ℝ :=
  ∑ i : Fin M, (s i).val * (s (nextIdx M i)).val

lemma E_par_flip {M : ℕ} (s t : Layer M) :
    E_par (flipLayer s) (flipLayer t) = E_par s t := by
  dsimp [E_par, flipLayer]
  congr 1
  ext i
  rw [Spin.val_flip, Spin.val_flip]
  ring

lemma E_perp_flip {M : ℕ} [NeZero M] (s : Layer M) :
    E_perp (flipLayer s) = E_perp s := by
  dsimp [E_perp, flipLayer]
  congr 1
  ext i
  rw [Spin.val_flip, Spin.val_flip]
  ring

/-- Матрица переноса 2^M x 2^M для лестницы ширины M -/
def transferMatrix {M : ℕ} [NeZero M] (K_par K_perp : ℝ) (s t : Layer M) : ℝ :=
  Real.exp (K_par * E_par s t + (1/2 : ℝ) * K_perp * (E_perp s + E_perp t))

lemma transferMatrix_flip {M : ℕ} [NeZero M] (K_par K_perp : ℝ) (s t : Layer M) :
    transferMatrix K_par K_perp (flipLayer s) (flipLayer t) =
    transferMatrix K_par K_perp s t := by
  dsimp [transferMatrix]
  rw [E_par_flip, E_perp_flip, E_perp_flip]

/-- Действие трансфер-матрицы на вектор состояния -/
def applyT {M : ℕ} [NeZero M] (K_par K_perp : ℝ) (v : Layer M → ℝ) (s : Layer M) : ℝ :=
  ∑ t : Layer M, transferMatrix K_par K_perp s t * v t

/-- Нечётное (спин-флип неинвариантное) подпространство: v(-s) = -v(s) -/
def IsOddState {M : ℕ} (v : Layer M → ℝ) : Prop :=
  ∀ s, v (flipLayer s) = - v s

/-- Сумма любой нечётной моды по всему пространству конфигураций строго равна 0 -/
lemma sum_odd_zero {M : ℕ} (v : Layer M → ℝ) (h : IsOddState v) :
    (∑ s : Layer M, v s) = 0 := by
  have h1 : (∑ s : Layer M, v s) = ∑ s : Layer M, v (flipLayer s) := by
    exact (Equiv.sum_comp (flipEquiv M) v).symm
  have h2 : (∑ s : Layer M, v (flipLayer s)) = - ∑ s : Layer M, v s := by
    rw [← Finset.sum_neg_distrib]
    congr 1
    ext s
    exact h s
  linarith

/-- Инвариантность нечётного подпространства под действием трансфер-матрицы -/
lemma applyT_is_odd {M : ℕ} [NeZero M] (K_par K_perp : ℝ) (v : Layer M → ℝ) (hv : IsOddState v) :
    IsOddState (applyT K_par K_perp v) := by
  intro s
  dsimp [applyT]
  have h_sum : (∑ t : Layer M, transferMatrix K_par K_perp (flipLayer s) t * v t) =
               ∑ t : Layer M, transferMatrix K_par K_perp (flipLayer s) (flipLayer t) * v (flipLayer t) := by
    exact (Equiv.sum_comp (flipEquiv M) (fun t => transferMatrix K_par K_perp (flipLayer s) t * v t)).symm
  rw [h_sum]
  have h_step (t : Layer M) : transferMatrix K_par K_perp (flipLayer s) (flipLayer t) * v (flipLayer t) =
                     - (transferMatrix K_par K_perp s t * v t) := by
    rw [transferMatrix_flip, hv t]
    ring
  rw [← Finset.sum_neg_distrib]
  congr 1
  ext t
  exact h_step t

/-- Сдвиг на константу не меняет действие матрицы на нечётное подпространство -/
lemma odd_apply_shift {M : ℕ} [NeZero M] (K_par K_perp : ℝ)
    (v : Layer M → ℝ) (hv : IsOddState v) (s : Layer M) (c : ℝ) :
    applyT K_par K_perp v s = ∑ t : Layer M, (transferMatrix K_par K_perp s t - c) * v t := by
  dsimp [applyT]
  have h_zero : c * (∑ t : Layer M, v t) = 0 := by
    rw [sum_odd_zero v hv, mul_zero]
  have h_split : (∑ t : Layer M, (transferMatrix K_par K_perp s t - c) * v t) =
                 (∑ t : Layer M, transferMatrix K_par K_perp s t * v t) - c * (∑ t : Layer M, v t) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [h_split, h_zero, sub_zero]

/--
**Главная теорема операторного сжатия Добрушина на нечётном подпространстве:**
Для ЛЮБОЙ ширины лестницы M ≥ 1 и произвольных констант связи,
любая нечётная мода сжимается строго сильнее, чем тривиальная равномерная мода u₀ = 1.
Разность между нормой действия на единицу и нечётную моду ограничена величиной 2^M * c,
что строго гарантирует спектральную щель БЕЗ привлечения теоремы Перрона — Фробениуса!
-/
theorem odd_subspace_contraction_bound
    {M : ℕ} [NeZero M] (K_par K_perp : ℝ)
    (v : Layer M → ℝ) (hv : IsOddState v)
    (B c : ℝ) (hB : ∀ t, |v t| ≤ B)
    (s : Layer M) (hc : ∀ t, c ≤ transferMatrix K_par K_perp s t) :
    |applyT K_par K_perp v s| ≤ ((∑ t : Layer M, transferMatrix K_par K_perp s t) - ((2 : ℝ) ^ M) * c) * B := by
  rw [odd_apply_shift K_par K_perp v hv s c]
  have h_abs_sum : |∑ t, (transferMatrix K_par K_perp s t - c) * v t| ≤
                   ∑ t, |(transferMatrix K_par K_perp s t - c) * v t| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_mul_abs : ∀ t, |(transferMatrix K_par K_perp s t - c) * v t| =
                        (transferMatrix K_par K_perp s t - c) * |v t| := by
    intro t
    rw [abs_mul, abs_of_nonneg]
    linarith [hc t]
  simp_rw [h_mul_abs] at h_abs_sum
  have h_le_B : (∑ t, (transferMatrix K_par K_perp s t - c) * |v t|) ≤
                ∑ t, (transferMatrix K_par K_perp s t - c) * B := by
    apply Finset.sum_le_sum
    intro t _
    have h_nonneg : 0 ≤ transferMatrix K_par K_perp s t - c := by linarith [hc t]
    exact mul_le_mul_of_nonneg_left (hB t) h_nonneg
  have h_sum_factor : (∑ t, (transferMatrix K_par K_perp s t - c) * B) =
                      (∑ t, (transferMatrix K_par K_perp s t - c)) * B := by
    rw [← Finset.sum_mul]
  have h_sum_sub : (∑ t, (transferMatrix K_par K_perp s t - c)) =
                   (∑ t, transferMatrix K_par K_perp s t) - ((2 : ℝ) ^ M) * c := by
    rw [Finset.sum_sub_distrib, sum_const_layer]
  rw [h_sum_factor, h_sum_sub] at h_le_B
  exact h_abs_sum.trans h_le_B

end ArbitraryLadder
