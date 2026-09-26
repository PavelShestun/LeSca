import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

open BigOperators Finset

/-!
===============================================================================
1. ДИСКРЕТНЫЕ СПИНЫ И СИММЕТРИИ
===============================================================================
-/

/-- Дискретный спин Изинга: вверх (+1) или вниз (-1) -/
inductive Spin : Type
  | up   : Spin
  | down : Spin
  deriving DecidableEq, Repr

namespace Spin

/-- Отображение спина в вещественное число: +1 или -1 -/
def val : Spin → ℝ
  | up   => 1
  | down => -1

/-- Операция переворота спина (spin-flip) -/
def flip : Spin → Spin
  | up   => down
  | down => up

@[simp]
theorem val_flip (s : Spin) : (flip s).val = - s.val := by
  cases s
  · rfl
  · dsimp [flip, val]
    ring

@[simp]
theorem flip_flip (s : Spin) : flip (flip s) = s := by
  cases s <;> rfl

instance : Fintype Spin where
  elems := {up, down}
  complete := by intro s; cases s <;> simp

@[simp]
lemma card_spin : Fintype.card Spin = 2 := rfl

end Spin

/-!
===============================================================================
2. КОНФИГУРАЦИИ И ИНВОЛЮЦИЯ Z_2
===============================================================================
-/

/-- Конфигурация спинов на произвольном множестве узлов V -/
abbrev Config (V : Type*) := V → Spin

/-- Глобальный переворот всех спинов -/
def flipConfig {V : Type*} (σ : Config V) : Config V :=
  fun i => Spin.flip (σ i)

@[simp]
theorem flipConfig_involutive {V : Type*} (σ : Config V) :
    flipConfig (flipConfig σ) = σ := by
  funext i
  exact Spin.flip_flip (σ i)

/-!
===============================================================================
3. ГАМИЛЬТОНИАН И СИММЕТРИЯ ПЕРЕВОРОТА СПИНОВ
===============================================================================
-/

variable {V : Type*} [Fintype V]

/--
Гамильтониан модели Изинга:
H(σ) = - (1/2) * ∑_{i, j} J_{ij} σ_i σ_j - h * ∑_i σ_i.
-/
def isingHamiltonian (J : V → V → ℝ) (h : ℝ) (σ : Config V) : ℝ :=
  - (1 / 2 : ℝ) * (∑ i : V, ∑ j : V, J i j * (σ i).val * (σ j).val) -
  h * (∑ i : V, (σ i).val)

/--
**Теорема о Z_2-симметрии гамильтониана (Spin-Flip Symmetry).**
При h = 0 энергия не меняется при одновременном перевороте всех спинов: H(-σ) = H(σ).
-/
theorem hamiltonian_spin_flip_symmetry (J : V → V → ℝ) (σ : Config V) :
    isingHamiltonian J 0 (flipConfig σ) = isingHamiltonian J 0 σ := by
  dsimp [isingHamiltonian, flipConfig]
  have h_pair : ∀ i j : V,
      J i j * (Spin.flip (σ i)).val * (Spin.flip (σ j)).val =
      J i j * (σ i).val * (σ j).val := by
    intro i j
    rw [Spin.val_flip, Spin.val_flip]
    ring
  simp_rw [h_pair]
  simp only [zero_mul, sub_zero]

/-!
===============================================================================
4. СТАТИСТИЧЕСКАЯ СУММА И МЕРА ГИББСА
===============================================================================
-/

-- Подключаем разрешимость равенства узлов только для конфигураций статистической суммы
variable [DecidableEq V]

/-- Статистическая сумма Z(β) = ∑_σ exp(-β * H(σ)) -/
def partitionFunction (J : V → V → ℝ) (h β : ℝ) : ℝ :=
  ∑ σ : Config V, Real.exp (-β * isingHamiltonian J h σ)

/--
**Теорема: Статистическая сумма строго положительна (Z > 0) для любой непустой решётки.**
-/
theorem partitionFunction_pos
    [Nonempty V] (J : V → V → ℝ) (h β : ℝ) :
    0 < partitionFunction J h β := by
  dsimp [partitionFunction]
  have h_nonempty : (Finset.univ : Finset (Config V)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact ⟨fun _ => Spin.up⟩
  apply Finset.sum_pos'
  · intro σ _
    exact (Real.exp_pos _).le
  · obtain ⟨σ₀, _⟩ := h_nonempty
    exact ⟨σ₀, Finset.mem_univ _, Real.exp_pos _⟩

/-- Мера Гиббса P(σ) = exp(-β H(σ)) / Z -/
def gibbsWeight (J : V → V → ℝ) (h β : ℝ) (σ : Config V) : ℝ :=
  Real.exp (-β * isingHamiltonian J h σ) / partitionFunction J h β

/--
**Теорема нормировки: полная сумма вероятностей Гиббса равна 1.**
-/
theorem gibbsWeight_normalized
    [Nonempty V] (J : V → V → ℝ) (h β : ℝ) :
    (∑ σ : Config V, gibbsWeight J h β σ) = 1 := by
  dsimp [gibbsWeight]
  have hZ_pos := partitionFunction_pos J h β
  have hZ_ne : partitionFunction J h β ≠ 0 := ne_of_gt hZ_pos
  have h_div : (fun σ => Real.exp (-β * isingHamiltonian J h σ) / partitionFunction J h β) =
               (fun σ => Real.exp (-β * isingHamiltonian J h σ) * (partitionFunction J h β)⁻¹) := by
    funext σ
    rw [div_eq_mul_inv]
  rw [h_div, ← Finset.sum_mul]
  dsimp [partitionFunction]
  exact mul_inv_cancel₀ hZ_ne

/-!
===============================================================================
5. РЕНОРМАЛИЗАЦИОННАЯ ГРУППА ДЛЯ 1D ИЗИНГА (ДЕЦИМАЦИЯ)
===============================================================================
-/

/-- Преобразование константы связи K = βJ при децимации: K' = (1/2) * ln(cosh(2K)) -/
def isingDecimation (K : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (Real.cosh (2 * K))

/--
**Фундаментальное свойство РГ одномерной модели Изинга:**
При любой конечной положительной температуре (K > 0) шаг децимации строго уменьшает связь:
  T(K) < K.
Поток РГ уносит систему к K* = 0 (нет фазового перехода в 1D при T > 0).
-/
theorem ising_decimation_contraction (K : ℝ) (hK : 0 < K) :
    isingDecimation K < K := by
  dsimp [isingDecimation]
  have h_cosh_pos : 0 < Real.cosh (2 * K) := Real.cosh_pos (2 * K)
  have h_cosh_lt : Real.cosh (2 * K) < Real.exp (2 * K) := by
    rw [Real.cosh_eq]
    -- Скобки согласованы с Real.cosh_eq: exp(-(2 * K))
    have h_lt : Real.exp (-(2 * K)) < Real.exp (2 * K) := by
      rw [Real.exp_lt_exp]
      linarith
    linarith
  have h_log_lt : Real.log (Real.cosh (2 * K)) < 2 * K := by
    have h := (Real.log_lt_log_iff h_cosh_pos (Real.exp_pos (2 * K))).mpr h_cosh_lt
    rw [Real.log_exp] at h
    exact h
  linarith
