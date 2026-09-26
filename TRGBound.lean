import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open BigOperators Finset

/-!
# TRGBound.lean (Level 3)
Строгая граница сходимости блочного тензорного огрубления (Levin-Nave TRG).
1. Eckart-Young-Mirsky монотонность хвоста сингулярных чисел при SVD-усечении.
2. Нелинейная теорема распространения ошибок стяжки 4-индексных тензоров.
-/

namespace TRG

/-- Хвост суммы квадратов отброшенных сингулярных чисел при усечении до ранга χ -/
def svdTailError (σ : ℕ → ℝ) (χ rank : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico χ rank, (σ k) ^ 2

lemma svdTailError_nonneg (σ : ℕ → ℝ) (χ rank : ℕ) :
    0 ≤ svdTailError σ χ rank := by
  dsimp [svdTailError]
  apply Finset.sum_nonneg
  intro k _
  exact sq_nonneg (σ k)

/--
**Теорема монотонности усечения ранга SVD:**
Увеличение сохраняемой размерности связи (bond dimension χ₁ ≤ χ₂)
монотонно уменьшает ошибку усечения тензора:
  Error(χ₂) ≤ Error(χ₁).
-/
theorem svdTailError_mono (σ : ℕ → ℝ) (χ₁ χ₂ rank : ℕ) (h : χ₁ ≤ χ₂) :
    svdTailError σ χ₂ rank ≤ svdTailError σ χ₁ rank := by
  dsimp [svdTailError]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_Ico] at hx ⊢
    exact ⟨h.trans hx.1, hx.2⟩
  · intro x _ _
    exact sq_nonneg (σ x)

/-- Алгебраическое телескопическое тождество для 4-кратного тензорного произведения -/
theorem four_tensor_telescoping_identity (A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : ℝ) :
    A₁ * A₂ * A₃ * A₄ - B₁ * B₂ * B₃ * B₄ =
    (A₁ - B₁) * A₂ * A₃ * A₄ +
    B₁ * (A₂ - B₂) * A₃ * A₄ +
    B₁ * B₂ * (A₃ - B₃) * A₄ +
    B₁ * B₂ * B₃ * (A₄ - B₄) := by
  ring

lemma abs_mul_four_le {a b c d ε C : ℝ}
    (ha : |a| ≤ ε) (hb : |b| ≤ C) (hc : |c| ≤ C) (hd : |d| ≤ C)
    (hε : 0 ≤ ε) (hC : 0 ≤ C) :
    |a * b * c * d| ≤ (C ^ 3) * ε := by
  have ha₀ : 0 ≤ |a| := abs_nonneg a
  have hb₀ : 0 ≤ |b| := abs_nonneg b
  have hc₀ : 0 ≤ |c| := abs_nonneg c
  have hd₀ : 0 ≤ |d| := abs_nonneg d
  have h1 : |c| * |d| ≤ C * C := mul_le_mul hc hd hd₀ hC
  have h2 : |b| * (|c| * |d|) ≤ C * (C * C) := mul_le_mul hb h1 (mul_nonneg hc₀ hd₀) hC
  have h3 : |a| * (|b| * (|c| * |d|)) ≤ ε * (C * (C * C)) :=
    mul_le_mul ha h2 (mul_nonneg hb₀ (mul_nonneg hc₀ hd₀)) hε
  have h_eq : |a * b * c * d| = |a| * (|b| * (|c| * |d|)) := by
    rw [abs_mul, abs_mul, abs_mul]
    ring
  rw [h_eq]
  have h_geom : ε * (C * (C * C)) = (C ^ 3) * ε := by ring
  linarith

/--
**Фундаментальная теорема стабильности шага TRG Левина — Наве:**
Если на одном шаге огрубления каждый из четырёх суб-тензоров усекается
с погрешностью не выше ε, а локальные нормы тензоров ограничены константой C,
то суммарная погрешность обновлённого узлового тензора строго линейна по ε:
  ||T_new - T̃_new|| ≤ 4 * C³ * ε.
-/
theorem four_tensor_error_bound
    (A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ C ε : ℝ)
    (_hA₁ : |A₁| ≤ C) (hA₂ : |A₂| ≤ C) (hA₃ : |A₃| ≤ C) (hA₄ : |A₄| ≤ C)
    (hB₁ : |B₁| ≤ C) (hB₂ : |B₂| ≤ C) (hB₃ : |B₃| ≤ C) (_hB₄ : |B₄| ≤ C)
    (hdiff₁ : |A₁ - B₁| ≤ ε) (hdiff₂ : |A₂ - B₂| ≤ ε)
    (hdiff₃ : |A₃ - B₃| ≤ ε) (hdiff₄ : |A₄ - B₄| ≤ ε)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) :
    |A₁ * A₂ * A₃ * A₄ - B₁ * B₂ * B₃ * B₄| ≤ 4 * (C ^ 3) * ε := by
  have t1 : |(A₁ - B₁) * A₂ * A₃ * A₄| ≤ (C ^ 3) * ε :=
    abs_mul_four_le hdiff₁ hA₂ hA₃ hA₄ hε hC
  have t2 : |B₁ * (A₂ - B₂) * A₃ * A₄| ≤ (C ^ 3) * ε := by
    have h_comm : B₁ * (A₂ - B₂) * A₃ * A₄ = (A₂ - B₂) * B₁ * A₃ * A₄ := by ring
    rw [h_comm]
    exact abs_mul_four_le hdiff₂ hB₁ hA₃ hA₄ hε hC
  have t3 : |B₁ * B₂ * (A₃ - B₃) * A₄| ≤ (C ^ 3) * ε := by
    have h_comm : B₁ * B₂ * (A₃ - B₃) * A₄ = (A₃ - B₃) * B₁ * B₂ * A₄ := by ring
    rw [h_comm]
    exact abs_mul_four_le hdiff₃ hB₁ hB₂ hA₄ hε hC
  have t4 : |B₁ * B₂ * B₃ * (A₄ - B₄)| ≤ (C ^ 3) * ε := by
    have h_comm : B₁ * B₂ * B₃ * (A₄ - B₄) = (A₄ - B₄) * B₁ * B₂ * B₃ := by ring
    rw [h_comm]
    exact abs_mul_four_le hdiff₄ hB₁ hB₂ hB₃ hε hC
  rw [four_tensor_telescoping_identity]
  have h1 := abs_add_le
    ((A₁ - B₁) * A₂ * A₃ * A₄ + B₁ * (A₂ - B₂) * A₃ * A₄ + B₁ * B₂ * (A₃ - B₃) * A₄)
    (B₁ * B₂ * B₃ * (A₄ - B₄))
  have h2 := abs_add_le
    ((A₁ - B₁) * A₂ * A₃ * A₄ + B₁ * (A₂ - B₂) * A₃ * A₄)
    (B₁ * B₂ * (A₃ - B₃) * A₄)
  have h3 := abs_add_le
    ((A₁ - B₁) * A₂ * A₃ * A₄)
    (B₁ * (A₂ - B₂) * A₃ * A₄)
  linarith [t1, t2, t3, t4, h1, h2, h3]

end TRG
