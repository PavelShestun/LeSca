import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section

open BigOperators Finset

/-!
# TransferMatrixRG.lean
Алгебраическая теория ренормализационной группы через матрицу переноса:
1. Матрица переноса 1D модели Изинга T(s, s') = exp(K * s * s').
2. Фундаментальная теорема: T(K)² = C₀(K) * T(K') (квадрат матрицы тождественен шагу РГ).
3. Инвариантность следа и статсуммы кольца Tr(T²) = C₀ Tr(T').
4. Спектральная задача: собственные значения λ₁ = 2 cosh(K) и λ₂ = 2 sinh(K).
5. Тождество Крамерса — Ванье: tanh(K') = (tanh K)².
6. Теорема сжатия корреляционной длины: ξ(K') = (1/2) * ξ(K).
-/

namespace TransferMatrixRG

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

/-!
===============================================================================
ЧАСТЬ 1: МАТРИЦА ПЕРЕНОСА И ЕЁ КВАДРАТ КАК ШАГ РГ
===============================================================================
-/

/-- Элемент матрицы переноса T(s, s') = exp(K * s * s') -/
def transferMatrix (K : ℝ) (s s' : Spin) : ℝ :=
  Real.exp (K * s.val * s'.val)

/-- Умножение матриц на пространстве состояний Spin × Spin -/
def matMul (A B : Spin → Spin → ℝ) (s s' : Spin) : ℝ :=
  ∑ s'' : Spin, A s s'' * B s'' s'

/-- След матрицы переноса -/
def matTrace (A : Spin → Spin → ℝ) : ℝ :=
  ∑ s : Spin, A s s

/-- Умножение матрицы на скаляр -/
def smulMat (c : ℝ) (A : Spin → Spin → ℝ) (s s' : Spin) : ℝ :=
  c * A s s'

/-- Ренормированная константа связи K' = (1/2) * ln(cosh(2K)) -/
def rgCoupling (K : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (Real.cosh (2 * K))

/-- Множитель свободной энергии C₀(K) = 2 * exp(K') = 2 * sqrt(cosh(2K)) -/
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

lemma rgPrefactor_mul_exp (K X : ℝ) :
    rgPrefactor K * Real.exp X = 2 * Real.exp (rgCoupling K + X) := by
  dsimp [rgPrefactor, rgCoupling]
  rw [mul_assoc, ← Real.exp_add]

/--
**Фундаментальная теорема алгебраической РГ (Квадрат трансфер-матрицы):**
Матричное произведение T(K) * T(K) в точности равно масштабированной
матрице переноса с ренормированной константой связи K':
  T(K)² = C₀(K) * T(K').
-/
theorem transfer_matrix_square_eq_rg (K : ℝ) (s₁ s₃ : Spin) :
    matMul (transferMatrix K) (transferMatrix K) s₁ s₃ =
    smulMat (rgPrefactor K) (transferMatrix (rgCoupling K)) s₁ s₃ := by
  dsimp [matMul, transferMatrix, smulMat]
  rw [Spin.sum_spin]
  cases s₁ <;> cases s₃
  · -- s₁ = +1, s₃ = +1
    dsimp [Spin.val]
    have h_lhs : Real.exp (K * 1 * 1) * Real.exp (K * 1 * 1) +
                 Real.exp (K * 1 * -1) * Real.exp (K * -1 * 1) =
                 2 * Real.cosh (2 * K) := by
      rw [← Real.exp_add, ← Real.exp_add]
      have h1 : K * 1 * 1 + K * 1 * 1 = 2 * K := by ring
      have h2 : K * 1 * -1 + K * -1 * 1 = - (2 * K) := by ring
      rw [h1, h2, Real.cosh_eq]
      ring
    have h_rhs : rgPrefactor K * Real.exp (rgCoupling K * 1 * 1) =
                 2 * Real.cosh (2 * K) := by
      rw [rgPrefactor_mul_exp]
      have h_add : rgCoupling K + rgCoupling K * 1 * 1 = 2 * rgCoupling K := by ring
      rw [h_add, exp_two_mul_rgCoupling]
    rw [h_lhs, h_rhs]
  · -- s₁ = +1, s₃ = -1
    dsimp [Spin.val]
    have h_lhs : Real.exp (K * 1 * 1) * Real.exp (K * 1 * -1) +
                 Real.exp (K * 1 * -1) * Real.exp (K * -1 * -1) = 2 := by
      rw [← Real.exp_add, ← Real.exp_add]
      have h1 : K * 1 * 1 + K * 1 * -1 = 0 := by ring
      have h2 : K * 1 * -1 + K * -1 * -1 = 0 := by ring
      rw [h1, h2, Real.exp_zero]
      norm_num
    have h_rhs : rgPrefactor K * Real.exp (rgCoupling K * 1 * -1) = 2 := by
      rw [rgPrefactor_mul_exp]
      have h_add : rgCoupling K + rgCoupling K * 1 * -1 = 0 := by ring
      rw [h_add, Real.exp_zero, mul_one]
    rw [h_lhs, h_rhs]
  · -- s₁ = -1, s₃ = +1
    dsimp [Spin.val]
    have h_lhs : Real.exp (K * -1 * 1) * Real.exp (K * 1 * 1) +
                 Real.exp (K * -1 * -1) * Real.exp (K * -1 * 1) = 2 := by
      rw [← Real.exp_add, ← Real.exp_add]
      have h1 : K * -1 * 1 + K * 1 * 1 = 0 := by ring
      have h2 : K * -1 * -1 + K * -1 * 1 = 0 := by ring
      rw [h1, h2, Real.exp_zero]
      norm_num
    have h_rhs : rgPrefactor K * Real.exp (rgCoupling K * -1 * 1) = 2 := by
      rw [rgPrefactor_mul_exp]
      have h_add : rgCoupling K + rgCoupling K * -1 * 1 = 0 := by ring
      rw [h_add, Real.exp_zero, mul_one]
    rw [h_lhs, h_rhs]
  · -- s₁ = -1, s₃ = -1
    dsimp [Spin.val]
    have h_lhs : Real.exp (K * -1 * 1) * Real.exp (K * 1 * -1) +
                 Real.exp (K * -1 * -1) * Real.exp (K * -1 * -1) =
                 2 * Real.cosh (2 * K) := by
      rw [← Real.exp_add, ← Real.exp_add]
      have h1 : K * -1 * 1 + K * 1 * -1 = - (2 * K) := by ring
      have h2 : K * -1 * -1 + K * -1 * -1 = 2 * K := by ring
      rw [h1, h2, add_comm, Real.cosh_eq]
      ring
    have h_rhs : rgPrefactor K * Real.exp (rgCoupling K * -1 * -1) =
                 2 * Real.cosh (2 * K) := by
      rw [rgPrefactor_mul_exp]
      have h_add : rgCoupling K + rgCoupling K * -1 * -1 = 2 * rgCoupling K := by ring
      rw [h_add, exp_two_mul_rgCoupling]
    rw [h_lhs, h_rhs]

/--
**Теорема о сохранении следа:**
След квадрата матрицы переноса равен масштабированному следу ренормированной матрицы:
  Tr(T(K)²) = C₀(K) * Tr(T(K')).
-/
theorem trace_transfer_matrix_square (K : ℝ) :
    matTrace (matMul (transferMatrix K) (transferMatrix K)) =
    rgPrefactor K * matTrace (transferMatrix (rgCoupling K)) := by
  dsimp [matTrace]
  have h (s : Spin) :
      matMul (transferMatrix K) (transferMatrix K) s s =
      rgPrefactor K * transferMatrix (rgCoupling K) s s := by
    have h_sq := transfer_matrix_square_eq_rg K s s
    dsimp [smulMat] at h_sq
    exact h_sq
  simp_rw [h]
  rw [← Finset.mul_sum]

/-!
===============================================================================
ЧАСТЬ 2: СПЕКТРАЛЬНОЕ РАЗЛОЖЕНИЕ МАТРИЦЫ ПЕРЕНОСА
===============================================================================
-/

/-- Симметричный собственный вектор: v₁(s) = 1 -/
def eigenvecSymm (_s : Spin) : ℝ := 1

/-- Антисимметричный собственный вектор: v₂(s) = s.val -/
def eigenvecAntisymm (s : Spin) : ℝ := s.val

/--
**Первое собственное значение λ₁ = 2 cosh(K):**
T(K) * v₁ = (2 cosh K) * v₁.
-/
theorem eigenval_symm (K : ℝ) (s : Spin) :
    (∑ s' : Spin, transferMatrix K s s' * eigenvecSymm s') =
    2 * Real.cosh K * eigenvecSymm s := by
  rw [Spin.sum_spin]
  cases s
  · dsimp [transferMatrix, eigenvecSymm, Spin.val]
    have h1 : K * 1 * 1 = K := by ring
    have h2 : K * 1 * -1 = -K := by ring
    rw [h1, h2, mul_one, mul_one, Real.cosh_eq]
    ring
  · dsimp [transferMatrix, eigenvecSymm, Spin.val]
    have h1 : K * -1 * 1 = -K := by ring
    have h2 : K * -1 * -1 = K := by ring
    rw [h1, h2, mul_one, mul_one, add_comm, Real.cosh_eq]
    ring

/--
**Второе собственное значение λ₂ = 2 sinh(K):**
T(K) * v₂ = (2 sinh K) * v₂.
-/
theorem eigenval_antisymm (K : ℝ) (s : Spin) :
    (∑ s' : Spin, transferMatrix K s s' * eigenvecAntisymm s') =
    2 * Real.sinh K * eigenvecAntisymm s := by
  rw [Spin.sum_spin]
  cases s
  · dsimp [transferMatrix, eigenvecAntisymm, Spin.val]
    have h1 : K * 1 * 1 = K := by ring
    have h2 : K * 1 * -1 = -K := by ring
    rw [h1, h2, mul_one, Real.sinh_eq]
    ring
  · dsimp [transferMatrix, eigenvecAntisymm, Spin.val]
    have h1 : K * -1 * 1 = -K := by ring
    have h2 : K * -1 * -1 = K := by ring
    rw [h1, h2, mul_one, Real.sinh_eq]
    ring

/-!
===============================================================================
ЧАСТЬ 3: СКЕЙЛИНГ КОРРЕЛЯЦИОННОЙ ДЛИНЫ ξ(K') = (1/2) * ξ(K)
===============================================================================
-/

/-- Отношение спиновых компонент (гиперболический тангенс tanh K) -/
def spinRatio (K : ℝ) : ℝ :=
  (Real.exp K - Real.exp (-K)) / (Real.exp K + Real.exp (-K))

/-- Корреляционная длина одномерной цепочки: ξ(K) = - 1 / ln(spinRatio K) -/
def correlationLength (K : ℝ) : ℝ :=
  - (1 / Real.log (spinRatio K))

lemma spinRatio_pos (K : ℝ) (hK : 0 < K) : 0 < spinRatio K := by
  dsimp [spinRatio]
  have hnum : 0 < Real.exp K - Real.exp (-K) := by
    have h_lt : -K < K := by linarith
    rw [sub_pos, Real.exp_lt_exp]
    exact h_lt
  have hden : 0 < Real.exp K + Real.exp (-K) :=
    add_pos (Real.exp_pos K) (Real.exp_pos (-K))
  exact div_pos hnum hden

/--
**Тождество Крамерса — Ванье для шага децимации:**
  tanh(K') = (tanh K)².
-/
theorem kramers_wannier_rg_identity (K : ℝ) :
    spinRatio (rgCoupling K) = (spinRatio K) ^ 2 := by
  let u := Real.exp K
  let v := Real.exp (-K)
  have huv : u * v = 1 := by
    dsimp [u, v]
    rw [← Real.exp_add]
    have h0 : K + -K = 0 := by ring
    rw [h0, Real.exp_zero]
  have hu2 : Real.exp (2 * K) = u ^ 2 := by
    dsimp [u]; rw [sq, ← Real.exp_add]; ring_nf
  have hv2 : Real.exp (- (2 * K)) = v ^ 2 := by
    dsimp [v]; rw [sq, ← Real.exp_add]; ring_nf
  have h_cosh2 : Real.cosh (2 * K) = (u ^ 2 + v ^ 2) / 2 := by
    rw [Real.cosh_eq, hu2, hv2]
  have h_cosh_sub : Real.cosh (2 * K) - 1 = (u - v) ^ 2 / 2 := by
    rw [h_cosh2]
    calc (u ^ 2 + v ^ 2) / 2 - 1
      _ = (u ^ 2 - 2 * (u * v) + v ^ 2) / 2 := by rw [huv]; ring
      _ = (u - v) ^ 2 / 2 := by ring
  have h_cosh_add : Real.cosh (2 * K) + 1 = (u + v) ^ 2 / 2 := by
    rw [h_cosh2]
    calc (u ^ 2 + v ^ 2) / 2 + 1
      _ = (u ^ 2 + 2 * (u * v) + v ^ 2) / 2 := by rw [huv]; ring
      _ = (u + v) ^ 2 / 2 := by ring
  dsimp [spinRatio]
  have h_ratio_rg : (Real.exp (rgCoupling K) - Real.exp (- rgCoupling K)) /
                    (Real.exp (rgCoupling K) + Real.exp (- rgCoupling K)) =
                    (Real.cosh (2 * K) - 1) / (Real.cosh (2 * K) + 1) := by
    have h_exp2 := exp_two_mul_rgCoupling K
    have h_mul_rg : (Real.exp (rgCoupling K) - Real.exp (- rgCoupling K)) /
                    (Real.exp (rgCoupling K) + Real.exp (- rgCoupling K)) =
                    (Real.exp (2 * rgCoupling K) - 1) /
                    (Real.exp (2 * rgCoupling K) + 1) := by
      let e := Real.exp (rgCoupling K)
      have he_pos : 0 < e := Real.exp_pos _
      have he_ne : e ≠ 0 := ne_of_gt he_pos
      have h_inv : Real.exp (- rgCoupling K) = e⁻¹ := by
        dsimp [e]; rw [Real.exp_neg]
      have h_sq : Real.exp (2 * rgCoupling K) = e ^ 2 := by
        dsimp [e]; rw [sq, ← Real.exp_add]; ring_nf
      rw [h_inv, h_sq]
      calc (e - e⁻¹) / (e + e⁻¹)
        _ = ((e - e⁻¹) * e) / ((e + e⁻¹) * e) := by rw [mul_div_mul_right _ _ he_ne]
        _ = (e ^ 2 - 1) / (e ^ 2 + 1) := by
            have h1 : (e - e⁻¹) * e = e ^ 2 - 1 := by
              calc (e - e⁻¹) * e = e * e - e⁻¹ * e := by ring
                _ = e ^ 2 - 1 := by rw [inv_mul_cancel₀ he_ne, sq]
            have h2 : (e + e⁻¹) * e = e ^ 2 + 1 := by
              calc (e + e⁻¹) * e = e * e + e⁻¹ * e := by ring
                _ = e ^ 2 + 1 := by rw [inv_mul_cancel₀ he_ne, sq]
            rw [h1, h2]
    rw [h_mul_rg, h_exp2]
  rw [h_ratio_rg, h_cosh_sub, h_cosh_add]
  have h_div_two : ((u - v) ^ 2 / 2) / ((u + v) ^ 2 / 2) =
                   (u - v) ^ 2 / (u + v) ^ 2 := by
    rw [div_div_div_comm]
    norm_num
  rw [h_div_two, ← div_pow]

/--
**Фундаментальная теорема сжатия корреляционной длины (Decimation Halving):**
При шаге РГ-децимации с масштабным фактором b = 2 физическая корреляционная
длина цепочки в единицах новой решётки уменьшается ровно в два раза:
  ξ(K') = (1/2) * ξ(K).
-/
theorem correlation_length_decimation_halved (K : ℝ) (hK : 0 < K) :
    correlationLength (rgCoupling K) = (1 / 2 : ℝ) * correlationLength K := by
  dsimp [correlationLength]
  have h_kw := kramers_wannier_rg_identity K
  rw [h_kw, sq]
  have h_pos := spinRatio_pos K hK
  rw [Real.log_mul (ne_of_gt h_pos) (ne_of_gt h_pos)]
  have h_add : Real.log (spinRatio K) + Real.log (spinRatio K) =
               2 * Real.log (spinRatio K) := by ring
  rw [h_add]
  have h_div : (1 : ℝ) / (2 * Real.log (spinRatio K)) =
               (1 / 2 : ℝ) * (1 / Real.log (spinRatio K)) := by ring
  rw [h_div]
  ring

end TransferMatrixRG
