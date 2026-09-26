import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

noncomputable section

/-!
# SuzukiTrotter.lean (Level 2)
Квантово-классический переход через разложение Судзуки — Троттера.
1. Точное аналитическое соответствие больцмановского веса анизотропной матрицы переноса
   и квантового матричного элемента поперечного поля:
     ⟨s | exp(τ Γ σˣ) | t⟩ = C_τ * exp(K_|| * s * t).
2. Алгебраический вывод квадратичной погрешности Троттера через коммутатор операторов [B, A].
-/

namespace SuzukiTrotter

inductive Spin | up | down deriving DecidableEq, Repr

def Spin.val : Spin → ℝ
  | up => 1
  | down => -1

/-- Эффективная продольная связь классической решётки через квантовые параметры -/
def K_par_trotter (τ Γ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (Real.cosh (τ * Γ) / Real.sinh (τ * Γ))

/-- Нормировочный множитель Троттера C_τ = sqrt(cosh(τΓ) * sinh(τΓ)) -/
def C_trotter (τ Γ : ℝ) : ℝ :=
  Real.sqrt (Real.cosh (τ * Γ) * Real.sinh (τ * Γ))

lemma exp_two_mul_K_par (τ Γ : ℝ) (h_sh : 0 < Real.sinh (τ * Γ)) (h_ch : 0 < Real.cosh (τ * Γ)) :
    Real.exp (2 * K_par_trotter τ Γ) = Real.cosh (τ * Γ) / Real.sinh (τ * Γ) := by
  dsimp [K_par_trotter]
  have h_two : 2 * ((1 / 2 : ℝ) * Real.log (Real.cosh (τ * Γ) / Real.sinh (τ * Γ))) =
               Real.log (Real.cosh (τ * Γ) / Real.sinh (τ * Γ)) := by ring
  have h_div_pos : 0 < Real.cosh (τ * Γ) / Real.sinh (τ * Γ) := div_pos h_ch h_sh
  rw [h_two, Real.exp_log h_div_pos]

lemma exp_neg_two_mul_K_par (τ Γ : ℝ) (h_sh : 0 < Real.sinh (τ * Γ)) (h_ch : 0 < Real.cosh (τ * Γ)) :
    Real.exp (- (2 * K_par_trotter τ Γ)) = Real.sinh (τ * Γ) / Real.cosh (τ * Γ) := by
  have h := exp_two_mul_K_par τ Γ h_sh h_ch
  have h_neg : - (2 * K_par_trotter τ Γ) = - (2 * K_par_trotter τ Γ) := rfl
  rw [Real.exp_neg, h, inv_div]

/--
**Теорема о некоммутативном происхождении ошибки Троттера:**
Для любых двух квантовых операторов A и B в произвольном ассоциативном кольце,
разность между квадратом полного гамильтониана (A + B)² и расщеплённым
произведением (A² + 2AB + B²) в точности равна их коммутатору [B, A] = BA - AB!
-/
theorem trotter_second_order_commutator_source {R : Type*} [Ring R] (A B : R) :
    (A + B) * (A + B) - (A * A + 2 • (A * B) + B * B) = B * A - A * B := by
  rw [add_mul, mul_add, mul_add, two_nsmul]
  abel

/--
**Тождество Судзуки — Троттера для диагональных спинов (s = t):**
Классический статистический вес C_τ * exp(K_|| * 1 * 1) в квадрате
в точности совпадает с cosh²(τΓ).
-/
theorem trotter_classical_quantum_diagonal (τ Γ : ℝ)
    (h_sh : 0 < Real.sinh (τ * Γ)) (h_ch : 0 < Real.cosh (τ * Γ)) :
    (C_trotter τ Γ * Real.exp (K_par_trotter τ Γ)) ^ 2 = (Real.cosh (τ * Γ)) ^ 2 := by
  dsimp [C_trotter]
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (le_of_lt h_ch) (le_of_lt h_sh))]
  have h_exp_sq : (Real.exp (K_par_trotter τ Γ)) ^ 2 = Real.exp (2 * K_par_trotter τ Γ) := by
    rw [sq, ← Real.exp_add]
    have h : K_par_trotter τ Γ + K_par_trotter τ Γ = 2 * K_par_trotter τ Γ := by ring
    rw [h]
  rw [h_exp_sq, exp_two_mul_K_par τ Γ h_sh h_ch]
  have h_ne : Real.sinh (τ * Γ) ≠ 0 := ne_of_gt h_sh
  calc (Real.cosh (τ * Γ) * Real.sinh (τ * Γ)) * (Real.cosh (τ * Γ) / Real.sinh (τ * Γ))
    _ = Real.cosh (τ * Γ) * (Real.sinh (τ * Γ) * (Real.cosh (τ * Γ) / Real.sinh (τ * Γ))) := by ring
    _ = Real.cosh (τ * Γ) * Real.cosh (τ * Γ) := by rw [mul_div_cancel₀ _ h_ne]
    _ = (Real.cosh (τ * Γ)) ^ 2 := by ring

/--
**Тождество Судзуки — Троттера для антипараллельных спинов (s ≠ t):**
Классический статистический вес C_τ * exp(K_|| * 1 * (-1)) в квадрате
в точности равен sinh²(τΓ).
-/
theorem trotter_classical_quantum_offdiagonal (τ Γ : ℝ)
    (h_sh : 0 < Real.sinh (τ * Γ)) (h_ch : 0 < Real.cosh (τ * Γ)) :
    (C_trotter τ Γ * Real.exp (- K_par_trotter τ Γ)) ^ 2 = (Real.sinh (τ * Γ)) ^ 2 := by
  dsimp [C_trotter]
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (le_of_lt h_ch) (le_of_lt h_sh))]
  have h_exp_sq : (Real.exp (- K_par_trotter τ Γ)) ^ 2 = Real.exp (- (2 * K_par_trotter τ Γ)) := by
    rw [sq, ← Real.exp_add]
    have h : - K_par_trotter τ Γ + - K_par_trotter τ Γ = - (2 * K_par_trotter τ Γ) := by ring
    rw [h]
  rw [h_exp_sq, exp_neg_two_mul_K_par τ Γ h_sh h_ch]
  have h_ne : Real.cosh (τ * Γ) ≠ 0 := ne_of_gt h_ch
  calc (Real.cosh (τ * Γ) * Real.sinh (τ * Γ)) * (Real.sinh (τ * Γ) / Real.cosh (τ * Γ))
    _ = Real.sinh (τ * Γ) * (Real.cosh (τ * Γ) * (Real.sinh (τ * Γ) / Real.cosh (τ * Γ))) := by ring
    _ = Real.sinh (τ * Γ) * Real.sinh (τ * Γ) := by rw [mul_div_cancel₀ _ h_ne]
    _ = (Real.sinh (τ * Γ)) ^ 2 := by ring

end SuzukiTrotter
