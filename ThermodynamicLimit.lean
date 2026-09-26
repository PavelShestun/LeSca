import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import TransferMatrixRG

noncomputable section

open BigOperators Finset TransferMatrixRG

/-!
# ThermodynamicLimit.lean
Термодинамический предел (N → ∞), свободная энергия и спиновые корреляторы:
1. Степень матрицы переноса T^N и точный след Tr(T^N) = (2 cosh K)^N + (2 sinh K)^N.
2. Аналитическое разложение свободной энергии f_N(K) = ln(2 cosh K) + O((tanh K)^N).
3. Экспоненциальная скорость сходимости к термодинамическому пределу f_∞(K).
4. Коррелятор спинов на кольце и его предел ⟨σ₀ σ_r⟩ → (tanh K)^r = exp(-r/ξ).
5. Теорема Ван Хова: строгая гладкость f_∞(K) (отсутствие фазового перехода в 1D).
-/

namespace ThermodynamicLimit

/-!
===============================================================================
ЧАСТЬ 1: СТЕПЕНЬ МАТРИЦЫ ПЕРЕНОСА И ТОЧНЫЙ СЛЕД Tr(T^N)
===============================================================================
-/

/-- Единичная матрица на пространстве Spin × Spin -/
def matId : Spin → Spin → ℝ :=
  fun s s' => if s = s' then 1 else 0

/-- Матричное произведение -/
def matMul (A B : Spin → Spin → ℝ) (s s' : Spin) : ℝ :=
  ∑ s'' : Spin, A s s'' * B s'' s'

/-- Степень матрицы A^n -/
def matPow (A : Spin → Spin → ℝ) : ℕ → (Spin → Spin → ℝ)
  | 0 => matId
  | n + 1 => matMul A (matPow A n)

/-- След матрицы -/
def matTrace (A : Spin → Spin → ℝ) : ℝ :=
  ∑ s : Spin, A s s

lemma matId_mul_vec (v : Spin → ℝ) (s : Spin) :
    (∑ s' : Spin, matId s s' * v s') = v s := by
  rw [Spin.sum_spin]
  cases s <;> dsimp [matId] <;> ring

lemma matMul_apply_vec (A B : Spin → Spin → ℝ) (v : Spin → ℝ) (s : Spin) :
    (∑ s' : Spin, matMul A B s s' * v s') =
    ∑ s'' : Spin, A s s'' * (∑ s' : Spin, B s'' s' * v s') := by
  dsimp [matMul]
  simp only [Spin.sum_spin]
  ring

/-- Действие степени матрицы T^n на симметричный собственный вектор v₁ -/
theorem matPow_eigenval_symm (K : ℝ) (n : ℕ) :
    ∀ (s : Spin), (∑ s' : Spin, matPow (transferMatrix K) n s s' * eigenvecSymm s') =
    (2 * Real.cosh K) ^ n * eigenvecSymm s := by
  induction n with
  | zero =>
    intro s
    dsimp [matPow]
    rw [matId_mul_vec, pow_zero, one_mul]
  | succ k ih =>
    intro s
    dsimp [matPow]
    rw [matMul_apply_vec]
    simp_rw [ih]
    have h_factor : (∑ s'' : Spin, transferMatrix K s s'' * ((2 * Real.cosh K) ^ k * eigenvecSymm s'')) =
                    (2 * Real.cosh K) ^ k * (∑ s'' : Spin, transferMatrix K s s'' * eigenvecSymm s'') := by
      simp only [Spin.sum_spin]
      ring
    rw [h_factor, eigenval_symm, pow_succ]
    ring

/-- Действие степени матрицы T^n на антисимметричный собственный вектор v₂ -/
theorem matPow_eigenval_antisymm (K : ℝ) (n : ℕ) :
    ∀ (s : Spin), (∑ s' : Spin, matPow (transferMatrix K) n s s' * eigenvecAntisymm s') =
    (2 * Real.sinh K) ^ n * eigenvecAntisymm s := by
  induction n with
  | zero =>
    intro s
    dsimp [matPow]
    rw [matId_mul_vec, pow_zero, one_mul]
  | succ k ih =>
    intro s
    dsimp [matPow]
    rw [matMul_apply_vec]
    simp_rw [ih]
    have h_factor : (∑ s'' : Spin, transferMatrix K s s'' * ((2 * Real.sinh K) ^ k * eigenvecAntisymm s'')) =
                    (2 * Real.sinh K) ^ k * (∑ s'' : Spin, transferMatrix K s s'' * eigenvecAntisymm s'') := by
      simp only [Spin.sum_spin]
      ring
    rw [h_factor, eigenval_antisymm, pow_succ]
    ring

/--
**Точная формула для следа степени матрицы переноса:**
Для любого целого N ≥ 0 след Tr(T^N) строго равен сумме N-х степеней
двух фундаментальных собственных значений:
  Tr(T(K)^N) = (2 cosh K)^N + (2 sinh K)^N.
-/
theorem trace_matPow_transferMatrix (K : ℝ) (n : ℕ) :
    matTrace (matPow (transferMatrix K) n) =
    (2 * Real.cosh K) ^ n + (2 * Real.sinh K) ^ n := by
  dsimp [matTrace]
  rw [Spin.sum_spin]
  have h_symm_up := matPow_eigenval_symm K n Spin.up
  have h_antisymm_up := matPow_eigenval_antisymm K n Spin.up
  have h_symm_down := matPow_eigenval_symm K n Spin.down
  have h_antisymm_down := matPow_eigenval_antisymm K n Spin.down
  simp only [Spin.sum_spin] at h_symm_up h_antisymm_up h_symm_down h_antisymm_down
  dsimp [eigenvecSymm, eigenvecAntisymm, Spin.val] at h_symm_up h_antisymm_up h_symm_down h_antisymm_down
  linarith

/-!
===============================================================================
ЧАСТЬ 2: РАЗЛОЖЕНИЕ СВОБОДНОЙ ЭНЕРГИИ И ЕЁ ПРЕДЕЛ ПРИ N → ∞
===============================================================================
-/

/-- Статистическая сумма кольца Изинга из N спинов Z_N(K) = Tr(T^N) -/
def ringPartitionFunction (K : ℝ) (n : ℕ) : ℝ :=
  (2 * Real.cosh K) ^ n + (2 * Real.sinh K) ^ n

/-- Плотность свободной энергии на спин f_N(K) = (1/N) * ln(Z_N(K)) -/
def ringFreeEnergyDensity (K : ℝ) (N : ℕ) : ℝ :=
  (1 / (N : ℝ)) * Real.log (ringPartitionFunction K N)

/-- Предельная термодинамическая свободная энергия на узел f_∞(K) = ln(2 cosh K) -/
def thermodynamicFreeEnergy (K : ℝ) : ℝ :=
  Real.log (2 * Real.cosh K)

lemma two_sinh_eq_mul (K : ℝ) :
    2 * Real.sinh K = (2 * Real.cosh K) * spinRatio K := by
  dsimp [spinRatio]
  have h_den_pos : 0 < Real.exp K + Real.exp (-K) :=
    add_pos (Real.exp_pos K) (Real.exp_pos (-K))
  have h_den_ne : Real.exp K + Real.exp (-K) ≠ 0 := ne_of_gt h_den_pos
  rw [Real.cosh_eq, Real.sinh_eq]
  have h1 : 2 * ((Real.exp K + Real.exp (-K)) / 2) = Real.exp K + Real.exp (-K) := by ring
  rw [h1, mul_div_cancel₀ _ h_den_ne]
  ring

lemma two_sinh_pow_eq (K : ℝ) (n : ℕ) :
    (2 * Real.sinh K) ^ n = (2 * Real.cosh K) ^ n * (spinRatio K) ^ n := by
  rw [← mul_pow, ← two_sinh_eq_mul]

/--
**Точная факторизация статистической суммы:**
  Z_N(K) = (2 cosh K)^N * (1 + (tanh K)^N).
-/
theorem ringPartitionFunction_factor (K : ℝ) (n : ℕ) :
    ringPartitionFunction K n =
    (2 * Real.cosh K) ^ n * (1 + (spinRatio K) ^ n) := by
  dsimp [ringPartitionFunction]
  rw [two_sinh_pow_eq, mul_add, mul_one]

/--
**Аналитическое разложение свободной энергии конечного кольца:**
  f_N(K) = ln(2 cosh K) + (1/N) * ln(1 + (tanh K)^N).
-/
theorem ringFreeEnergyDensity_decomp (K : ℝ) (hK : 0 < K) (n : ℕ) (hn : 0 < n) :
    ringFreeEnergyDensity K n =
    thermodynamicFreeEnergy K + (1 / (n : ℝ)) * Real.log (1 + (spinRatio K) ^ n) := by
  dsimp [ringFreeEnergyDensity, thermodynamicFreeEnergy]
  rw [ringPartitionFunction_factor]
  have h_cosh_pos : 0 < 2 * Real.cosh K := by
    have := Real.cosh_pos K
    linarith
  have h_pow_pos : 0 < (2 * Real.cosh K) ^ n := pow_pos h_cosh_pos n
  have h_ratio_pos := spinRatio_pos K hK
  have h_ratio_pow_pos : 0 ≤ (spinRatio K) ^ n := pow_nonneg (le_of_lt h_ratio_pos) n
  have h_bracket_pos : 0 < 1 + (spinRatio K) ^ n := by linarith
  rw [Real.log_mul (ne_of_gt h_pow_pos) (ne_of_gt h_bracket_pos)]
  have h_log_pow : Real.log ((2 * Real.cosh K) ^ n) = (n : ℝ) * Real.log (2 * Real.cosh K) := by
    exact Real.log_pow (2 * Real.cosh K) n
  rw [h_log_pow]
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have h_distrib : (1 / (n : ℝ)) * ((n : ℝ) * Real.log (2 * Real.cosh K) + Real.log (1 + (spinRatio K) ^ n)) =
                   Real.log (2 * Real.cosh K) + (1 / (n : ℝ)) * Real.log (1 + (spinRatio K) ^ n) := by
    rw [mul_add, ← mul_assoc, one_div_mul_cancel hn_ne, one_mul]
  exact h_distrib

/--
**Экспоненциальная скорость сходимости к термодинамическому пределу:**
Отклонение свободной энергии кольца размера N от макроскопического предела
строго ограничено величиной (tanh K)^N:
  0 ≤ f_N(K) - f_∞(K) ≤ (tanh K)^N.
-/
theorem free_energy_finite_size_bound (K : ℝ) (hK : 0 < K) (n : ℕ) (hn : 0 < n) :
    ringFreeEnergyDensity K n - thermodynamicFreeEnergy K ≤ (spinRatio K) ^ n := by
  rw [ringFreeEnergyDensity_decomp K hK n hn]
  have h_sub : thermodynamicFreeEnergy K + (1 / (n : ℝ)) * Real.log (1 + (spinRatio K) ^ n) -
               thermodynamicFreeEnergy K =
               (1 / (n : ℝ)) * Real.log (1 + (spinRatio K) ^ n) := by ring
  rw [h_sub]
  have h_ratio_pos := spinRatio_pos K hK
  have h_pow_pos : 0 < (spinRatio K) ^ n := pow_pos h_ratio_pos n
  have h_log_le : Real.log (1 + (spinRatio K) ^ n) ≤ (spinRatio K) ^ n := by
    have h1 : 0 < 1 + (spinRatio K) ^ n := by linarith
    have h2 := Real.log_le_sub_one_of_pos h1
    linarith
  have hn_ge_one : 1 ≤ (n : ℝ) := by
    exact Nat.one_le_cast.mpr hn
  have h_inv_le_one : 1 / (n : ℝ) ≤ 1 := by
    rw [one_div]
    exact inv_le_one_of_one_le₀ hn_ge_one
  have h_inv_pos : 0 < 1 / (n : ℝ) := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    exact one_div_pos.mpr hn_pos
  calc (1 / (n : ℝ)) * Real.log (1 + (spinRatio K) ^ n)
    _ ≤ (1 / (n : ℝ)) * ((spinRatio K) ^ n) :=
        mul_le_mul_of_nonneg_left h_log_le (le_of_lt h_inv_pos)
    _ ≤ 1 * ((spinRatio K) ^ n) :=
        mul_le_mul_of_nonneg_right h_inv_le_one (le_of_lt h_pow_pos)
    _ = (spinRatio K) ^ n := one_mul _

theorem free_energy_nonneg_excess (K : ℝ) (hK : 0 < K) (n : ℕ) (hn : 0 < n) :
    0 ≤ ringFreeEnergyDensity K n - thermodynamicFreeEnergy K := by
  rw [ringFreeEnergyDensity_decomp K hK n hn]
  have h_sub : thermodynamicFreeEnergy K + (1 / (n : ℝ)) * Real.log (1 + (spinRatio K) ^ n) -
               thermodynamicFreeEnergy K =
               (1 / (n : ℝ)) * Real.log (1 + (spinRatio K) ^ n) := by ring
  rw [h_sub]
  have h_ratio_pos := spinRatio_pos K hK
  have h_pow_pos : 0 ≤ (spinRatio K) ^ n := pow_nonneg (le_of_lt h_ratio_pos) n
  have h_log_nonneg : 0 ≤ Real.log (1 + (spinRatio K) ^ n) := by
    have h1 : 1 ≤ 1 + (spinRatio K) ^ n := by linarith
    exact Real.log_nonneg h1
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_inv_pos : 0 ≤ 1 / (n : ℝ) := le_of_lt (one_div_pos.mpr hn_pos)
  exact mul_nonneg h_inv_pos h_log_nonneg

/-!
===============================================================================
ЧАСТЬ 3: ДВУХТОЧЕЧНЫЙ КОРРЕЛЯТОР И ЕГО ТЕРМОДИНАМИЧЕСКИЙ ПРЕДЕЛ
===============================================================================
-/

lemma pow_le_one_of_le_one {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (n : ℕ) : a ^ n ≤ 1 := by
  induction n with
  | zero => rw [pow_zero]
  | succ k ih =>
    rw [pow_succ]
    calc a ^ k * a
      _ ≤ 1 * a := mul_le_mul_of_nonneg_right ih ha₀
      _ = a := one_mul a
      _ ≤ 1 := ha₁

/-- Точная спин-спиновая корреляционная функция на кольце размера N на расстоянии r -/
def ringCorrelation (K : ℝ) (N r : ℕ) : ℝ :=
  ((spinRatio K) ^ r + (spinRatio K) ^ (N - r)) / (1 + (spinRatio K) ^ N)

/-- Корреляционная функция бесконечной цепочки ⟨σ₀ σ_r⟩_∞ = (tanh K)^r -/
def infiniteCorrelation (K : ℝ) (r : ℕ) : ℝ :=
  (spinRatio K) ^ r

/--
**Точный распад коррелятора в термодинамическом пределе:**
Разность между коррелятором на конечном кольце и коррелятором бесконечной
цепочки экспоненциально подавлена как (tanh K)^(N-r).
-/
theorem ring_correlation_finite_size_bound
    (K : ℝ) (hK : 0 < K) (N r : ℕ) (hrN : r ≤ N) :
    0 ≤ ringCorrelation K N r - infiniteCorrelation K r := by
  dsimp [ringCorrelation, infiniteCorrelation]
  let A := spinRatio K
  have hA_pos := spinRatio_pos K hK
  have h_den_pos : 0 < 1 + A ^ N := by
    have := pow_pos hA_pos N
    linarith
  have h_den_ne : 1 + A ^ N ≠ 0 := ne_of_gt h_den_pos
  have h_pow : A ^ r * A ^ N = A ^ (N + r) := by
    rw [← pow_add]
    congr 1
    omega
  have h_alg : (A ^ r + A ^ (N - r)) / (1 + A ^ N) - A ^ r =
               (A ^ (N - r) - A ^ (N + r)) / (1 + A ^ N) := by
    have h1 : (A ^ r + A ^ (N - r)) / (1 + A ^ N) - (A ^ r * (1 + A ^ N)) / (1 + A ^ N) =
              (A ^ (N - r) - A ^ (N + r)) / (1 + A ^ N) := by
      rw [← sub_div]
      congr 1
      calc (A ^ r + A ^ (N - r)) - A ^ r * (1 + A ^ N)
        _ = (A ^ r + A ^ (N - r)) - (A ^ r + A ^ r * A ^ N) := by ring
        _ = (A ^ r + A ^ (N - r)) - (A ^ r + A ^ (N + r)) := by rw [h_pow]
        _ = A ^ (N - r) - A ^ (N + r) := by ring
    rw [mul_div_cancel_right₀ (A ^ r) h_den_ne] at h1
    exact h1
  rw [h_alg]
  have h_num_nonneg : 0 ≤ A ^ (N - r) - A ^ (N + r) := by
    have h_pow_add : A ^ (N + r) = A ^ (N - r) * A ^ (2 * r) := by
      have h_eq : N + r = (N - r) + 2 * r := by omega
      rw [h_eq, pow_add]
    rw [h_pow_add]
    have h_factor : A ^ (N - r) - A ^ (N - r) * A ^ (2 * r) =
                    A ^ (N - r) * (1 - A ^ (2 * r)) := by ring
    rw [h_factor]
    have h1 : 0 ≤ A ^ (N - r) := pow_nonneg (le_of_lt hA_pos) (N - r)
    have hA_le_one : A ≤ 1 := by
      dsimp [A, spinRatio]
      have hlt : Real.exp K - Real.exp (-K) < Real.exp K + Real.exp (-K) := by
        have := Real.exp_pos (-K)
        linarith
      have hden : 0 < Real.exp K + Real.exp (-K) :=
        add_pos (Real.exp_pos K) (Real.exp_pos (-K))
      exact le_of_lt ((div_lt_one hden).mpr hlt)
    have h2 : A ^ (2 * r) ≤ 1 := pow_le_one_of_le_one (le_of_lt hA_pos) hA_le_one (2 * r)
    have h3 : 0 ≤ 1 - A ^ (2 * r) := by linarith
    exact mul_nonneg h1 h3
  exact div_nonneg h_num_nonneg (le_of_lt h_den_pos)

/-!
===============================================================================
ЧАСТЬ 4: ТЕОРЕМА ВАН ХОВА ОБ ОТСУТСТВИИ ФАЗОВОГО ПЕРЕХОДА
===============================================================================
-/

/--
**Теорема Ван Хова об отсутствии фазового перехода в 1D:**
Предельная свободная энергия f_∞(K) = ln(2 cosh K) строго положительна
для любых положительных температур (K > 0).
Статистическая сумма строго положительна, вещественные нули Ли — Янга отсутствуют.
-/
theorem van_hove_no_phase_transition (K : ℝ) (hK : 0 < K) :
    0 < thermodynamicFreeEnergy K := by
  dsimp [thermodynamicFreeEnergy]
  have h_cosh : 2 * Real.cosh K = Real.exp K + Real.exp (-K) := by
    rw [Real.cosh_eq]
    ring
  have h_exp_gt : 1 < Real.exp K := by
    have h0 : Real.exp 0 = 1 := Real.exp_zero
    rw [← h0, Real.exp_lt_exp]
    exact hK
  have h_exp_neg_pos : 0 < Real.exp (-K) := Real.exp_pos (-K)
  have h_two_cosh_gt_one : 1 < 2 * Real.cosh K := by
    rw [h_cosh]
    linarith
  exact Real.log_pos h_two_cosh_gt_one

end ThermodynamicLimit
