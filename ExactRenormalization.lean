import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section

open BigOperators Finset

/-!
# ExactRenormalization.lean
Углублённая теория ренормализационной группы:
1. Микроскопический вывод 1D-децимации через частичный след статсуммы.
2. Точное сохранение статистической суммы при РГ-шаге Каданова.
3. Аналитическая траектория потока Вильсона — Фишера и экспоненциальная релаксация к IR-аттрактору.
4. Обобщённая однородность свободной энергии Видома и вывод скейлингового анзаца.
-/

namespace ExactRG

/-!
===============================================================================
ЧАСТЬ 1: МИКРОСКОПИЧЕСКИЙ ВЫВОД ДЕЦИМАЦИИ (ВЗЯТИЕ ЧАСТИЧНОГО СЛЕДА)
===============================================================================
-/

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
  · simp

end Spin

/-- Ренормированная константа связи K' после исключения промежуточного спина -/
def rgCoupling (K : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (Real.cosh (2 * K))

/-- Множитель свободной энергии на спин C₀(K) = 2 * (cosh(2K))^(1/2) -/
def rgPrefactor (K : ℝ) : ℝ :=
  2 * Real.exp ((1 / 2 : ℝ) * Real.log (Real.cosh (2 * K)))

lemma cosh_pos_two (K : ℝ) : 0 < Real.cosh (2 * K) :=
  Real.cosh_pos (2 * K)

lemma exp_two_mul_rgCoupling (K : ℝ) :
    Real.exp (2 * rgCoupling K) = Real.cosh (2 * K) := by
  dsimp [rgCoupling]
  have h2 : 2 * ((1 / 2 : ℝ) * Real.log (Real.cosh (2 * K))) =
            Real.log (Real.cosh (2 * K)) := by ring
  rw [h2, Real.exp_log (cosh_pos_two K)]

lemma exp_neg_two_mul_rgCoupling (K : ℝ) :
    Real.exp (- 2 * rgCoupling K) = (Real.cosh (2 * K))⁻¹ := by
  have h := exp_two_mul_rgCoupling K
  have h_neg : - 2 * rgCoupling K = - (2 * rgCoupling K) := by ring
  rw [h_neg, Real.exp_neg, h]

lemma rgPrefactor_mul_exp (K X : ℝ) :
    rgPrefactor K * Real.exp X = 2 * Real.exp (rgCoupling K + X) := by
  dsimp [rgPrefactor, rgCoupling]
  rw [mul_assoc, ← Real.exp_add]

/--
**Фундаментальная теорема микроскопической децимации:**
Для ЛЮБЫХ фиксированных граничных спинов s₁ и s₃ сумма больцмановских весов
по промежуточному спину s₂ в точности сворачивается в эффективное взаимодействие:
  ∑_{s₂} exp(K * s₂ * (s₁ + s₃)) = C₀(K) * exp(K' * s₁ * s₃).
-/
theorem microscopic_decimation_identity (K : ℝ) (s₁ s₃ : Spin) :
    (∑ s₂ : Spin, Real.exp (K * s₂.val * (s₁.val + s₃.val))) =
    rgPrefactor K * Real.exp (rgCoupling K * s₁.val * s₃.val) := by
  rw [Spin.sum_spin]
  cases s₁ <;> cases s₃
  · -- Случай: s₁ = +1, s₃ = +1
    dsimp [Spin.val]
    have h_lhs : Real.exp (K * 1 * (1 + 1)) + Real.exp (K * (-1) * (1 + 1)) =
                 2 * Real.cosh (2 * K) := by
      have h1 : K * 1 * (1 + 1) = 2 * K := by ring
      have h2 : K * (-1) * (1 + 1) = - (2 * K) := by ring
      rw [h1, h2, Real.cosh_eq]
      ring
    have h_rhs : rgPrefactor K * Real.exp (rgCoupling K * 1 * 1) =
                 2 * Real.cosh (2 * K) := by
      rw [rgPrefactor_mul_exp]
      have h_add : rgCoupling K + rgCoupling K * 1 * 1 = 2 * rgCoupling K := by ring
      rw [h_add, exp_two_mul_rgCoupling]
    rw [h_lhs, h_rhs]
  · -- Случай: s₁ = +1, s₃ = -1
    dsimp [Spin.val]
    have h_lhs : Real.exp (K * 1 * (1 + -1)) + Real.exp (K * (-1) * (1 + -1)) = 2 := by
      have h1 : K * 1 * (1 + -1) = 0 := by ring
      have h2 : K * (-1) * (1 + -1) = 0 := by ring
      rw [h1, h2, Real.exp_zero]
      norm_num
    have h_rhs : rgPrefactor K * Real.exp (rgCoupling K * 1 * -1) = 2 := by
      rw [rgPrefactor_mul_exp]
      have h_add : rgCoupling K + rgCoupling K * 1 * -1 = 0 := by ring
      rw [h_add, Real.exp_zero, mul_one]
    rw [h_lhs, h_rhs]
  · -- Случай: s₁ = -1, s₃ = +1
    dsimp [Spin.val]
    have h_lhs : Real.exp (K * 1 * (-1 + 1)) + Real.exp (K * (-1) * (-1 + 1)) = 2 := by
      have h1 : K * 1 * (-1 + 1) = 0 := by ring
      have h2 : K * (-1) * (-1 + 1) = 0 := by ring
      rw [h1, h2, Real.exp_zero]
      norm_num
    have h_rhs : rgPrefactor K * Real.exp (rgCoupling K * -1 * 1) = 2 := by
      rw [rgPrefactor_mul_exp]
      have h_add : rgCoupling K + rgCoupling K * -1 * 1 = 0 := by ring
      rw [h_add, Real.exp_zero, mul_one]
    rw [h_lhs, h_rhs]
  · -- Случай: s₁ = -1, s₃ = -1
    dsimp [Spin.val]
    have h_lhs : Real.exp (K * 1 * (-1 + -1)) + Real.exp (K * (-1) * (-1 + -1)) =
                 2 * Real.cosh (2 * K) := by
      have h1 : K * 1 * (-1 + -1) = - (2 * K) := by ring
      have h2 : K * (-1) * (-1 + -1) = 2 * K := by ring
      rw [h1, h2, add_comm, Real.cosh_eq]
      ring
    have h_rhs : rgPrefactor K * Real.exp (rgCoupling K * -1 * -1) =
                 2 * Real.cosh (2 * K) := by
      rw [rgPrefactor_mul_exp]
      have h_add : rgCoupling K + rgCoupling K * -1 * -1 = 2 * rgCoupling K := by ring
      rw [h_add, exp_two_mul_rgCoupling]
    rw [h_lhs, h_rhs]

/--
**Теорема о сохранении статистической суммы:**
При шаге децимации статсумма 3-спиновой открытой цепочки в точности равна
статсумме эффективной 2-спиновой цепочки с весовым множителем C₀(K):
  Z₃(K) = C₀(K) * Z₂(K').
-/
theorem partition_function_exact_decimation (K : ℝ) :
    (∑ s₁ : Spin, ∑ s₂ : Spin, ∑ s₃ : Spin,
      Real.exp (K * s₂.val * (s₁.val + s₃.val))) =
    rgPrefactor K * (∑ s₁ : Spin, ∑ s₃ : Spin,
      Real.exp (rgCoupling K * s₁.val * s₃.val)) := by
  have h_swap (s₁ : Spin) :
      (∑ s₂ : Spin, ∑ s₃ : Spin, Real.exp (K * s₂.val * (s₁.val + s₃.val))) =
      (∑ s₃ : Spin, ∑ s₂ : Spin, Real.exp (K * s₂.val * (s₁.val + s₃.val))) :=
    Finset.sum_comm
  have h_inner (s₁ : Spin) :
      (∑ s₃ : Spin, ∑ s₂ : Spin, Real.exp (K * s₂.val * (s₁.val + s₃.val))) =
      rgPrefactor K * ∑ s₃ : Spin, Real.exp (rgCoupling K * s₁.val * s₃.val) := by
    have h_step : ∀ s₃ : Spin, (∑ s₂ : Spin, Real.exp (K * s₂.val * (s₁.val + s₃.val))) =
        rgPrefactor K * Real.exp (rgCoupling K * s₁.val * s₃.val) :=
      fun s₃ => microscopic_decimation_identity K s₁ s₃
    simp_rw [h_step]
    rw [← Finset.mul_sum]
  calc (∑ s₁ : Spin, ∑ s₂ : Spin, ∑ s₃ : Spin, Real.exp (K * s₂.val * (s₁.val + s₃.val)))
    _ = ∑ s₁ : Spin, (∑ s₃ : Spin, ∑ s₂ : Spin, Real.exp (K * s₂.val * (s₁.val + s₃.val))) := by
        congr 1; ext s₁; exact h_swap s₁
    _ = ∑ s₁ : Spin, (rgPrefactor K * ∑ s₃ : Spin, Real.exp (rgCoupling K * s₁.val * s₃.val)) := by
        congr 1; ext s₁; exact h_inner s₁
    _ = rgPrefactor K * (∑ s₁ : Spin, ∑ s₃ : Spin, Real.exp (rgCoupling K * s₁.val * s₃.val)) := by
        rw [← Finset.mul_sum]

/-!
===============================================================================
ЧАСТЬ 2: ДИНАМИКА ПОТОКА РГ И ЭКСПОНЕНЦИАЛЬНЫЙ IR-АТТРАКТОР
===============================================================================
-/

/-- Аналитическая траектория g(ℓ) потока Вильсона — Фишера -/
def wilsonFisherTrajectory (ε b g₀ ℓ : ℝ) : ℝ :=
  (ε / b) / (1 + ((ε / b) / g₀ - 1) * Real.exp (- ε * ℓ))

/-- Проверка начального условия: при ℓ = 0 система стартует из затравочной связи g₀ -/
theorem wf_initial_condition (ε b g₀ : ℝ) (h_ratio : ε / b ≠ 0) :
    wilsonFisherTrajectory ε b g₀ 0 = g₀ := by
  dsimp [wilsonFisherTrajectory]
  have h_exp : Real.exp (- ε * 0) = 1 := by
    have h0 : - ε * 0 = 0 := by ring
    rw [h0, Real.exp_zero]
  rw [h_exp, mul_one]
  have h_denom : 1 + ((ε / b) / g₀ - 1) = (ε / b) / g₀ := by ring
  rw [h_denom]
  rw [div_div_eq_mul_div]
  exact mul_div_cancel_left₀ g₀ h_ratio

/-- Инвариантность неподвижной точки: если g₀ = g*, то g(ℓ) ≡ g* для всех ℓ -/
theorem wf_fixed_point_invariant (ε b ℓ : ℝ) (hb : b ≠ 0) (hε : ε ≠ 0) :
    wilsonFisherTrajectory ε b (ε / b) ℓ = ε / b := by
  dsimp [wilsonFisherTrajectory]
  have h_cancel : (ε / b) / (ε / b) = 1 := div_self (div_ne_zero hε hb)
  rw [h_cancel, sub_self, zero_mul, add_zero, div_one]

/--
**Теорема об экспоненциальной релаксации к точке Вильсона — Фишера:**
Отклонение связи от неподвижной точки |g(ℓ) - g*| затухает пропорционально exp(-εℓ).
-/
theorem wf_approach_rate (ε b g₀ ℓ : ℝ)
    (h_denom_ne : 1 + ((ε / b) / g₀ - 1) * Real.exp (- ε * ℓ) ≠ 0) :
    wilsonFisherTrajectory ε b g₀ ℓ - (ε / b) =
    - (ε / b) * (((ε / b) / g₀ - 1) * Real.exp (- ε * ℓ)) /
      (1 + ((ε / b) / g₀ - 1) * Real.exp (- ε * ℓ)) := by
  dsimp [wilsonFisherTrajectory]
  set A := ((ε / b) / g₀ - 1) * Real.exp (- ε * ℓ)
  set x := ε / b
  have h1 : x / (1 + A) - x * (1 + A) / (1 + A) = - x * A / (1 + A) := by
    rw [← sub_div]
    congr 1
    ring
  rw [mul_div_cancel_right₀ x h_denom_ne] at h1
  exact h1

/-!
===============================================================================
ЧАСТЬ 3: ОБОБЩЕННАЯ ОДНОРОДНОСТЬ ВИДОМА И ВЫВОД СКЕЙЛИНГОВОГО АНЗАЦА
===============================================================================
-/

/-- Свободная энергия удовлетворяет скейлинговой гипотезе Видома с масштабом b > 0 -/
def IsWidomScalingFreeEnergy (f : ℝ → ℝ → ℝ) (d y_t y_h : ℝ) : Prop :=
  ∀ (b : ℝ), 0 < b → ∀ (t h : ℝ),
    f t h = (b ^ (-d)) * f (b ^ y_t * t) (b ^ y_h * h)

/--
**Теорема вывода универсальной функции подобия Видома:**
Если термодинамический потенциал f(t, h) инвариантен относительно масштабирования РГ,
то выбором масштабного множителя b = t^(-1 / y_t) потенциал строго приводится
к каноническому виду f(t, h) = t^(d / y_t) * f(1, h / t^(y_h / y_t)).
-/
theorem widom_scaling_function_derivation
    (f : ℝ → ℝ → ℝ) (d y_t y_h : ℝ)
    (h_scale : IsWidomScalingFreeEnergy f d y_t y_h)
    (t h : ℝ) (ht : 0 < t) (h_yt : y_t ≠ 0) :
    f t h = (t ^ (d / y_t)) * f 1 (h * t ^ (- (y_h / y_t))) := by
  let b := t ^ (- (1 / y_t))
  have hb_pos : 0 < b := Real.rpow_pos_of_pos ht _
  have h_widom := h_scale b hb_pos t h
  rw [h_widom]
  have h_bt : b ^ y_t * t = 1 := by
    dsimp [b]
    rw [← Real.rpow_mul (le_of_lt ht)]
    have h_prod : - (1 / y_t) * y_t = -1 := by
      rw [neg_mul, one_div_mul_cancel h_yt]
    rw [h_prod, Real.rpow_neg_one, inv_mul_cancel₀ (ne_of_gt ht)]
  have h_bd : b ^ (-d) = t ^ (d / y_t) := by
    dsimp [b]
    rw [← Real.rpow_mul (le_of_lt ht)]
    have h_prod : - (1 / y_t) * (-d) = d / y_t := by ring
    rw [h_prod]
  have h_bh : b ^ y_h * h = h * t ^ (- (y_h / y_t)) := by
    dsimp [b]
    rw [← Real.rpow_mul (le_of_lt ht)]
    have h_prod : - (1 / y_t) * y_h = - (y_h / y_t) := by ring
    rw [h_prod, mul_comm]
  rw [h_bt, h_bd, h_bh]

end ExactRG
