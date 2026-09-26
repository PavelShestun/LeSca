import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace WidomTheory

/--
Функциональное уравнение однородности Видома для свободной энергии f(t, h):
f(t, h) = b^(-d) * f(b^(y_t) * t, b^(y_h) * h) для любого масштаба b > 0.
-/
def SatisfiesWidomScaling (f : ℝ → ℝ → ℝ) (d y_t y_h : ℝ) : Prop :=
  ∀ (b : ℝ), 0 < b → ∀ (t h : ℝ), 0 < t →
    f t h = (b ^ (-d)) * f (b ^ y_t * t) (b ^ y_h * h)

/--
Канонический вид свободной энергии через универсальную функцию масштабирования Φ:
f(t, h) = t^(d / y_t) * Φ(h * t^(- y_h / y_t)).
-/
def HasWidomForm (f : ℝ → ℝ → ℝ) (d y_t y_h : ℝ) (Φ : ℝ → ℝ) : Prop :=
  ∀ (t h : ℝ), 0 < t →
    f t h = (t ^ (d / y_t)) * Φ (h * t ^ (- (y_h / y_t)))

/--
**Главная теорема представления и классификации Видома:**
Свободная энергия f удовлетворяет функциональному уравнению скейлинга Видома
тогда и только тогда, когда существует функция масштабирования Φ(x), задающая
универсальное представление f(t, h) = t^(d / y_t) * Φ(h / t^Δ).
-/
theorem widom_representation_iff
    (f : ℝ → ℝ → ℝ) (d y_t y_h : ℝ) (h_yt : y_t ≠ 0) :
    SatisfiesWidomScaling f d y_t y_h ↔
    ∃ (Φ : ℝ → ℝ), HasWidomForm f d y_t y_h Φ := by
  constructor
  · intro h_scale
    use fun x => f 1 x
    intro t h ht
    let b := t ^ (- (1 / y_t))
    have hb_pos : 0 < b := Real.rpow_pos_of_pos ht _
    have h_widom := h_scale b hb_pos t h ht
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
  · rintro ⟨Φ, h_rep⟩
    intro b hb t h ht
    have h_scaled_t_pos : 0 < b ^ y_t * t := mul_pos (Real.rpow_pos_of_pos hb _) ht
    rw [h_rep t h ht]
    rw [h_rep (b ^ y_t * t) (b ^ y_h * h) h_scaled_t_pos]
    have h_pow_t : (b ^ y_t * t) ^ (d / y_t) = (b ^ d) * (t ^ (d / y_t)) := by
      rw [Real.mul_rpow (Real.rpow_nonneg (le_of_lt hb) _) (le_of_lt ht)]
      congr 1
      rw [← Real.rpow_mul (le_of_lt hb)]
      have h_cancel : y_t * (d / y_t) = d := by
        rw [mul_div_cancel₀ d h_yt]
      rw [h_cancel]
    have h_cancel_arg : y_t * (- (y_h / y_t)) = - y_h := by
      have h1 : y_t * (- (y_h / y_t)) = - (y_t * (y_h / y_t)) := by ring
      rw [h1, mul_div_cancel₀ y_h h_yt]
    have h_arg_b_cancel : b ^ y_h * b ^ (-y_h) = 1 := by
      rw [← Real.rpow_add hb]
      have h0 : y_h + -y_h = (0 : ℝ) := by ring
      rw [h0, Real.rpow_zero]
    have h_arg : (b ^ y_h * h) * (b ^ y_t * t) ^ (- (y_h / y_t)) =
                 h * t ^ (- (y_h / y_t)) := by
      rw [Real.mul_rpow (Real.rpow_nonneg (le_of_lt hb) _) (le_of_lt ht)]
      rw [← Real.rpow_mul (le_of_lt hb)]
      rw [h_cancel_arg]
      calc (b ^ y_h * h) * ((b ^ (-y_h)) * (t ^ (- (y_h / y_t))))
        _ = (b ^ y_h * b ^ (-y_h)) * (h * t ^ (- (y_h / y_t))) := by ring
        _ = 1 * (h * t ^ (- (y_h / y_t))) := by rw [h_arg_b_cancel]
        _ = h * t ^ (- (y_h / y_t)) := one_mul _
    rw [h_pow_t, h_arg]
    have h_bd_cancel : b ^ (-d) * b ^ d = 1 := by
      rw [← Real.rpow_add hb]
      have h0 : -d + d = (0 : ℝ) := by ring
      rw [h0, Real.rpow_zero]
    symm
    calc b ^ (-d) * ((b ^ d * t ^ (d / y_t)) * Φ (h * t ^ (- (y_h / y_t))))
      _ = (b ^ (-d) * b ^ d) * (t ^ (d / y_t) * Φ (h * t ^ (- (y_h / y_t)))) := by ring
      _ = 1 * (t ^ (d / y_t) * Φ (h * t ^ (- (y_h / y_t)))) := by rw [h_bd_cancel]
      _ = t ^ (d / y_t) * Φ (h * t ^ (- (y_h / y_t))) := one_mul _

/--
**Теорема единственности:**
Функция масштабирования Φ(x) определена однозначно и равна f(1, x).
-/
theorem widom_scaling_function_unique
    (f : ℝ → ℝ → ℝ) (d y_t y_h : ℝ) (Φ : ℝ → ℝ)
    (h_rep : HasWidomForm f d y_t y_h Φ) (x : ℝ) :
    Φ x = f 1 x := by
  have h1 := h_rep 1 x (by norm_num)
  rw [Real.one_rpow, one_mul] at h1
  have h_arg : x * 1 ^ (- (y_h / y_t)) = x := by
    rw [Real.one_rpow, mul_one]
  rw [h_arg] at h1
  exact h1.symm

end WidomTheory
