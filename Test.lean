import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic

-- Зададим размерность транскриптома: n генов
variable {n : ℕ}

-- В Mathlib вектор размерности n со стандартным евклидовым скалярным произведением
-- записывается как: EuclideanSpace ℝ (Fin n)
abbrev GeneProfile (n : ℕ) := EuclideanSpace ℝ (Fin n)

-- Определим понятие нормализованного профиля клетки (единичная норма: ‖u‖ = 1)
def IsNormalized (u : GeneProfile n) : Prop :=
  ‖u‖ = 1

-- ТЕОРЕМА О ГРАНИЦАХ СХОДСТВА ДВУХ КЛЕТОК:
-- Для любых двух нормализованных клеток u и v, их скалярное произведение (косинусное сходство)
-- строго ограничено единицей: ⟪u, v⟫_ℝ ≤ 1
theorem cell_cosine_similarity_le_one
    (u v : GeneProfile n)
    (hu : IsNormalized u)
    (hv : IsNormalized v) :
    @inner ℝ _ _ u v ≤ 1 := by
  -- 1. Вызываем общее неравенство Коши-Буняковского из Mathlib:
  -- real_inner_le_norm : ⟪u, v⟫ ≤ ‖u‖ * ‖v‖
  have h_cs := real_inner_le_norm u v
  -- 2. Подставляем условия нормализации клеток: ‖u‖ = 1 и ‖v‖ = 1
  dsimp [IsNormalized] at hu hv
  rw [hu, hv] at h_cs
  -- 3. Упрощаем 1 * 1 = 1
  ring_nf at h_cs
  -- 4. Получаем исходное неравенство
  exact h_cs


-- ТЕОРЕМА О СВЯЗИ ЕВКЛИДОВА РАССТОЯНИЯ И КОСИНУСНОГО СХОДСТВА:
-- Квадрат евклидова расстояния между нормализованными клетками
-- в точности равен удвоенному косинусному расстоянию: ‖u - v‖² = 2 * (1 - ⟪u, v⟫)
theorem euclidean_dist_sq_eq_two_mul_one_sub_cosine
    (u v : GeneProfile n)
    (hu : IsNormalized u)
    (hv : IsNormalized v) :
    ‖u - v‖^2 = 2 * (1 - @inner ℝ _ _ u v) := by
  -- Раскрываем формулу квадрата разности для нормы в гильбертовом пространстве:
  -- ‖u - v‖² = ‖u‖² - 2⟪u, v⟫ + ‖v‖²
  have h_exp := @norm_sub_sq_real (GeneProfile n) _ u v
  -- Подставляем ‖u‖ = 1 и ‖v‖ = 1
  dsimp [IsNormalized] at hu hv
  rw [hu, hv] at h_exp
  -- У нас есть: ‖u - v‖² = 1² - 2⟪u, v⟫ + 1²
  -- Осталась чистая школьная алгебра: доказать равенство раскрытых скобок!
  linear_combination h_exp
