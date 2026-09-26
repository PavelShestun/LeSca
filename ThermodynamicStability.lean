import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open BigOperators Finset

/-!
# Термодинамическая устойчивость, корреляторы и бета-функция Вильсона — Фишера
-/

/-!
===============================================================================
1. МАТЕМАТИЧЕСКОЕ ОЖИДАНИЕ ГИББСА И ТЕРМОДИНАМИЧЕСКИЕ НАБЛЮДАЕМЫЕ
===============================================================================
-/

section GibbsExpectation

inductive Spin | up | down deriving DecidableEq

namespace Spin

def val : Spin → ℝ
  | up => 1
  | down => -1

/-- Модуль значения любого спина всегда равен в точности 1 -/
@[simp]
lemma abs_val (s : Spin) : |s.val| = 1 := by
  cases s <;> (dsimp [val]; norm_num)

end Spin

instance : Fintype Spin where
  elems := {Spin.up, Spin.down}
  complete := by intro s; cases s <;> simp

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Config (V : Type*) := V → Spin
abbrev Observable (V : Type*) := Config V → ℝ

def isingH (J : V → V → ℝ) (h : ℝ) (σ : Config V) : ℝ :=
  - (1 / 2 : ℝ) * (∑ i : V, ∑ j : V, J i j * (σ i).val * (σ j).val) -
  h * (∑ i : V, (σ i).val)

def partitionFunction (J : V → V → ℝ) (h β : ℝ) : ℝ :=
  ∑ σ : Config V, Real.exp (-β * isingH J h σ)

lemma partitionFunction_pos [Nonempty V] (J : V → V → ℝ) (h β : ℝ) :
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

def gibbsWeight (J : V → V → ℝ) (h β : ℝ) (σ : Config V) : ℝ :=
  Real.exp (-β * isingH J h σ) / partitionFunction J h β

lemma gibbsWeight_pos [Nonempty V] (J : V → V → ℝ) (h β : ℝ) (σ : Config V) :
    0 < gibbsWeight J h β σ :=
  div_pos (Real.exp_pos _) (partitionFunction_pos J h β)

lemma gibbsWeight_nonneg [Nonempty V] (J : V → V → ℝ) (h β : ℝ) (σ : Config V) :
    0 ≤ gibbsWeight J h β σ :=
  (gibbsWeight_pos J h β σ).le

lemma gibbsWeight_sum_one [Nonempty V] (J : V → V → ℝ) (h β : ℝ) :
    (∑ σ : Config V, gibbsWeight J h β σ) = 1 := by
  dsimp [gibbsWeight]
  have hZ_pos := partitionFunction_pos J h β
  have hZ_ne : partitionFunction J h β ≠ 0 := ne_of_gt hZ_pos
  have h_div : (fun σ => Real.exp (-β * isingH J h σ) / partitionFunction J h β) =
               (fun σ => Real.exp (-β * isingH J h σ) * (partitionFunction J h β)⁻¹) := by
    funext σ; rw [div_eq_mul_inv]
  rw [h_div, ← Finset.sum_mul]
  dsimp [partitionFunction]
  exact mul_inv_cancel₀ hZ_ne

/-- Статистическое среднее наблюдаемой X по ансамблю Гиббса: ⟨X⟩ = ∑_σ P(σ) X(σ) -/
def gibbsExpectation [Nonempty V] (J : V → V → ℝ) (h β : ℝ) (X : Observable V) : ℝ :=
  ∑ σ : Config V, gibbsWeight J h β σ * X σ

/-- Среднее константы равно самой константе: ⟨c⟩ = c -/
theorem gibbsExpectation_const [Nonempty V] (J : V → V → ℝ) (h β : ℝ) (c : ℝ) :
    gibbsExpectation J h β (fun _ => c) = c := by
  dsimp [gibbsExpectation]
  rw [← Finset.sum_mul]
  have h_norm := gibbsWeight_sum_one J h β
  rw [h_norm, one_mul]

/-- Положительность функционала Гиббса: если X(σ) ≥ 0, то и ⟨X⟩ ≥ 0 -/
theorem gibbsExpectation_nonneg [Nonempty V] (J : V → V → ℝ) (h β : ℝ) (X : Observable V)
    (hX : ∀ σ, 0 ≤ X σ) :
    0 ≤ gibbsExpectation J h β X := by
  dsimp [gibbsExpectation]
  apply Finset.sum_nonneg
  intro σ _
  exact mul_nonneg (gibbsWeight_nonneg J h β σ) (hX σ)

/--
**Фундаментальная теорема об ограниченности наблюдаемых:**
Если наблюдаемая ограничена на микросостояниях |X(σ)| ≤ M,
то её среднее значение строго ограничено той же константой: |⟨X⟩| ≤ M.
-/
theorem gibbsExpectation_bound [Nonempty V] (J : V → V → ℝ) (h β : ℝ) (X : Observable V) (M : ℝ)
    (hM : ∀ σ, |X σ| ≤ M) :
    |gibbsExpectation J h β X| ≤ M := by
  dsimp [gibbsExpectation]
  have h_abs := Finset.abs_sum_le_sum_abs (fun σ => gibbsWeight J h β σ * X σ) Finset.univ
  have h_mul : ∀ σ, |gibbsWeight J h β σ * X σ| = gibbsWeight J h β σ * |X σ| := by
    intro σ
    rw [abs_mul, abs_of_nonneg (gibbsWeight_nonneg J h β σ)]
  simp_rw [h_mul] at h_abs
  have h_le : (∑ σ : Config V, gibbsWeight J h β σ * |X σ|) ≤
              (∑ σ : Config V, gibbsWeight J h β σ * M) := by
    apply Finset.sum_le_sum
    intro σ _
    exact mul_le_mul_of_nonneg_left (hM σ) (gibbsWeight_nonneg J h β σ)
  have h_sum_M : (∑ σ : Config V, gibbsWeight J h β σ * M) = M := by
    rw [← Finset.sum_mul, gibbsWeight_sum_one, one_mul]
  exact h_abs.trans (h_le.trans (le_of_eq h_sum_M))

end GibbsExpectation

/-!
===============================================================================
2. КОРРЕЛЯТОРЫ И ТЕРМОДИНАМИЧЕСКАЯ УСТОЙЧИВОСТЬ (χ ≥ 0)
===============================================================================
-/

section CorrelationAndStability

-- Объявляем только тип вершин, без лишних предположений о конечности
variable {V : Type*}

/-- Двухточечная спин-спиновая корреляционная функция: G(i, j)(σ) = σ_i * σ_j -/
def twoPointObservable (i j : V) : Observable V :=
  fun σ => (σ i).val * (σ j).val

lemma twoPoint_bounded (i j : V) (σ : Config V) :
    |twoPointObservable i j σ| ≤ 1 := by
  dsimp [twoPointObservable]
  rw [abs_mul, Spin.abs_val, Spin.abs_val, mul_one]

-- Подключаем структуры ансамбля Гиббса там, где они действительно нужны
variable [Fintype V] [DecidableEq V] [Nonempty V]

/--
**Теорема о насыщении двухточечного коррелятора:**
Для любых двух узлов i и j в решётке спин-спиновый коррелятор
всегда строго лежит в диапазоне [-1, 1]:
  |⟨σ_i * σ_j⟩| ≤ 1.
-/
theorem twoPoint_correlation_bounded (J : V → V → ℝ) (h β : ℝ) (i j : V) :
    |gibbsExpectation J h β (twoPointObservable i j)| ≤ 1 :=
  gibbsExpectation_bound J h β (twoPointObservable i j) 1 (twoPoint_bounded i j)

/-- Дисперсия наблюдаемой X: Var(X) = ⟨(X - ⟨X⟩)²⟩ -/
def gibbsVariance (J : V → V → ℝ) (h β : ℝ) (X : Observable V) : ℝ :=
  gibbsExpectation J h β (fun σ => (X σ - gibbsExpectation J h β X) ^ 2)

/--
**Теорема о неотрицательности дисперсии:**
Var(X) ≥ 0 для любой наблюдаемой X.
-/
theorem gibbsVariance_nonneg (J : V → V → ℝ) (h β : ℝ) (X : Observable V) :
    0 ≤ gibbsVariance J h β X := by
  dsimp [gibbsVariance]
  apply gibbsExpectation_nonneg
  intro σ
  exact sq_nonneg _

/-- Полная намагниченность решётки M(σ) = ∑_i σ_i -/
def totalMagObservable : Observable V :=
  fun σ => ∑ i : V, (σ i).val

/-- Магнитная восприимчивость χ = β * Var(M) -/
def magneticSusceptibility (J : V → V → ℝ) (h β : ℝ) : ℝ :=
  β * gibbsVariance J h β totalMagObservable

/--
**Фундаментальная теорема термодинамической устойчивости:**
Магнитная восприимчивость системы всегда неотрицательна при неотрицательной температуре:
  χ ≥ 0 при β ≥ 0.
-/
theorem thermodynamic_stability_susceptibility_nonneg
    (J : V → V → ℝ) (h β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ magneticSusceptibility J h β := by
  dsimp [magneticSusceptibility]
  exact mul_nonneg hβ (gibbsVariance_nonneg J h β totalMagObservable)

end CorrelationAndStability

/-!
===============================================================================
3. НЕПРЕРЫВНЫЙ ПОТОК РГ: β-ФУНКЦИЯ И НЕПОДВИЖНАЯ ТОЧКА ВИЛЬСОНА — ФИШЕРА
===============================================================================
-/

section ContinuousRGFlow

def betaFunction (ε b g : ℝ) : ℝ :=
  - ε * g + b * g ^ 2

def betaDerivative (ε b g : ℝ) : ℝ :=
  - ε + 2 * b * g

/--
**Теорема о нулях бета-функции (Классификация неподвижных точек):**
Уравнение β(g) = 0 имеет ровно два решения:
1) g* = 0 — тривиальная Гауссова точка.
2) g* = ε / b — нетривиальная точка Вильсона — Фишера.
-/
theorem wilson_fisher_fixed_points (ε b g : ℝ) (hb : b ≠ 0) :
    betaFunction ε b g = 0 ↔ g = 0 ∨ g = ε / b := by
  dsimp [betaFunction]
  have h_factor : - ε * g + b * g ^ 2 = g * (b * g - ε) := by ring
  rw [h_factor, mul_eq_zero]
  constructor
  · rintro (h1 | h2)
    · exact Or.inl h1
    · right
      have : b * g = ε := by linarith
      exact (eq_div_iff hb).mpr (by linarith)
  · rintro (h1 | h2)
    · exact Or.inl h1
    · right
      rw [h2]
      rw [mul_div_cancel₀ ε hb]
      ring

/--
**Теорема о неустойчивости Гауссовой точки ниже 4D (ε > 0):**
β'(0) = - ε < 0.
-/
theorem gaussian_fixed_point_ir_unstable (ε b : ℝ) (hε : 0 < ε) :
    betaDerivative ε b 0 < 0 := by
  dsimp [betaDerivative]
  linarith

/--
**Теорема об устойчивости точки Вильсона — Фишера (IR-Attractor):**
β'(ε / b) = + ε > 0.
-/
theorem wilson_fisher_ir_stable (ε b : ℝ) (hb : b ≠ 0) (hε : 0 < ε) :
    0 < betaDerivative ε b (ε / b) := by
  dsimp [betaDerivative]
  have h_cancel : 2 * b * (ε / b) = 2 * ε := by
    calc 2 * b * (ε / b) = 2 * (b * (ε / b)) := by ring
      _ = 2 * ε := by rw [mul_div_cancel₀ ε hb]
  rw [h_cancel]
  linarith

theorem wilson_fisher_coupling_pos (ε b : ℝ) (hε : 0 < ε) (hb : 0 < b) :
    0 < ε / b :=
  div_pos hε hb

end ContinuousRGFlow
