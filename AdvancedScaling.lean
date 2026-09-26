import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Asymptotics.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section

open Asymptotics Filter BigOperators Finset

/-!
===============================================================================
БАЗОВАЯ СТРУКТУРА ПОТОКА РГ
===============================================================================
-/

section DiscreteRG

variable {V : Type*}

def rgFlow (T : V → V) : ℕ → V → V
  | 0, v => v
  | n + 1, v => T (rgFlow T n v)

variable [SeminormedAddCommGroup V]

theorem rg_scaling_bound
    (T : V → V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hT : ∀ w : V, ‖T w‖ ≤ ρ * ‖w‖)
    (n : ℕ) (v : V) :
    ‖rgFlow T n v‖ ≤ (ρ ^ n) * ‖v‖ := by
  induction n with
  | zero =>
    dsimp [rgFlow]
    rw [pow_zero, one_mul]
  | succ k ih =>
    dsimp [rgFlow]
    have hstep : ‖T (rgFlow T k v)‖ ≤ ρ * ‖rgFlow T k v‖ := hT (rgFlow T k v)
    have hmul : ρ * ‖rgFlow T k v‖ ≤ ρ * ((ρ ^ k) * ‖v‖) :=
      mul_le_mul_of_nonneg_left ih hρ
    have h_assoc : ρ * ((ρ ^ k) * ‖v‖) = (ρ ^ (k + 1)) * ‖v‖ := by
      rw [← mul_assoc, mul_comm ρ (ρ ^ k), ← pow_succ]
    exact hstep.trans (hmul.trans (le_of_eq h_assoc))

end DiscreteRG

/-!
===============================================================================
ЧАСТЬ 1. АСИМПТОТИЧЕСКИЕ СКЕЙЛИНГОВЫЕ ОЦЕНКИ (LANDAU NOTATION / IsBigO)
===============================================================================
-/

section AsymptoticRG

variable {V : Type*} [SeminormedAddCommGroup V]

theorem rg_isBigO
    (T : V → V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hT : ∀ w : V, ‖T w‖ ≤ ρ * ‖w‖) (v : V) :
    IsBigO atTop (fun n => rgFlow T n v) (fun n => ρ ^ n) := by
  refine IsBigO.of_bound ‖v‖ (Eventually.of_forall (fun n => ?_))
  have h_bound := rg_scaling_bound T ρ hρ hT n v
  have h_le : ρ ^ n ≤ ‖ρ ^ n‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self (ρ ^ n)
  calc ‖rgFlow T n v‖
    _ ≤ (ρ ^ n) * ‖v‖ := h_bound
    _ = ‖v‖ * (ρ ^ n) := mul_comm (ρ ^ n) ‖v‖
    _ ≤ ‖v‖ * ‖ρ ^ n‖ := mul_le_mul_of_nonneg_left h_le (norm_nonneg v)

end AsymptoticRG

/-!
===============================================================================
ЧАСТЬ 2. НЕЛИНЕЙНЫЙ ШАГ РГ (КВАДРАТИЧНОЕ ВОЗМУЩЕНИЕ И ЛОКАЛЬНАЯ УСТОЙЧИВОСТЬ)
===============================================================================
-/

section NonLinearRG

variable {V : Type*} [SeminormedAddCommGroup V]

lemma nonlinear_step_contract
    (T : V → V) (ρ C r : ℝ) (hC : 0 ≤ C)
    (h_step : ∀ w : V, ‖w‖ ≤ r → ‖T w‖ ≤ ρ * ‖w‖ + C * ‖w‖ ^ 2)
    (w : V) (hw : ‖w‖ ≤ r) :
    ‖T w‖ ≤ (ρ + C * r) * ‖w‖ := by
  have h1 := h_step w hw
  have hw_sq : ‖w‖ ^ 2 ≤ r * ‖w‖ := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right hw (norm_nonneg w)
  have hC_mul : C * ‖w‖ ^ 2 ≤ C * (r * ‖w‖) :=
    mul_le_mul_of_nonneg_left hw_sq hC
  have h2 : ρ * ‖w‖ + C * ‖w‖ ^ 2 ≤ (ρ + C * r) * ‖w‖ := by
    linarith
  exact h1.trans h2

theorem nonlinear_rg_scaling
    (T : V → V) (ρ C r : ℝ) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (h_step : ∀ w : V, ‖w‖ ≤ r → ‖T w‖ ≤ ρ * ‖w‖ + C * ‖w‖ ^ 2)
    (h_contract : ρ + C * r ≤ 1)
    (v : V) (hv : ‖v‖ ≤ r) (n : ℕ) :
    ‖rgFlow T n v‖ ≤ ((ρ + C * r) ^ n) * ‖v‖ ∧ ‖rgFlow T n v‖ ≤ r := by
  let lam := ρ + C * r
  have hlam_nonneg : 0 ≤ lam := add_nonneg hρ (mul_nonneg hC hr)
  induction n with
  | zero =>
    dsimp [rgFlow]
    rw [pow_zero, one_mul]
    exact ⟨le_rfl, hv⟩
  | succ k ih =>
    obtain ⟨ih_decay, ih_ball⟩ := ih
    dsimp [rgFlow]
    have h_step_k := nonlinear_step_contract T ρ C r hC h_step (rgFlow T k v) ih_ball
    have h_decay : ‖T (rgFlow T k v)‖ ≤ (lam ^ (k + 1)) * ‖v‖ := by
      have h1 : lam * ‖rgFlow T k v‖ ≤ lam * ((lam ^ k) * ‖v‖) :=
        mul_le_mul_of_nonneg_left ih_decay hlam_nonneg
      have h_assoc : lam * ((lam ^ k) * ‖v‖) = (lam ^ (k + 1)) * ‖v‖ := by
        rw [← mul_assoc, mul_comm lam (lam ^ k), ← pow_succ]
      exact h_step_k.trans (h1.trans (le_of_eq h_assoc))
    have h_ball : ‖T (rgFlow T k v)‖ ≤ r := by
      have h1 : lam * ‖rgFlow T k v‖ ≤ r := by
        calc lam * ‖rgFlow T k v‖
          _ ≤ lam * r := mul_le_mul_of_nonneg_left ih_ball hlam_nonneg
          _ ≤ 1 * r := mul_le_mul_of_nonneg_right h_contract hr
          _ = r := one_mul r
      exact h_step_k.trans h1
    exact ⟨h_decay, h_ball⟩

end NonLinearRG

/-!
===============================================================================
ЧАСТЬ 3. БЛОЧНОЕ УСРЕДНЕНИЕ КАДАНОВА НА 1D РЕШЁТКЕ
===============================================================================
-/

section KadanoffLattice

def kadanoffAverage (N : ℕ) (ϕ : Fin (2 * N) → ℝ) (i : Fin N) : ℝ :=
  (1 / 2 : ℝ) * (ϕ ⟨2 * i.val, by omega⟩ + ϕ ⟨2 * i.val + 1, by omega⟩)

theorem kadanoff_sup_bound (N : ℕ) (ϕ : Fin (2 * N) → ℝ) (M : ℝ)
    (hM : ∀ j, |ϕ j| ≤ M) (i : Fin N) :
    |kadanoffAverage N ϕ i| ≤ M := by
  dsimp [kadanoffAverage]
  rw [abs_mul, abs_of_pos (by norm_num)]
  have h_tri : |ϕ ⟨2 * i.val, by omega⟩ + ϕ ⟨2 * i.val + 1, by omega⟩| ≤ M + M := by
    exact (abs_add_le _ _).trans (add_le_add (hM _) (hM _))
  linarith

end KadanoffLattice

/-!
===============================================================================
ЧАСТЬ 4. МНОГОМЕРНЫЕ РЕШЁТКИ ℤ^d И d-МЕРНЫЙ БЛОКИНГ КАДАНОВА
===============================================================================
-/

section MultidimKadanoffGrid

-- Используем имя Grid вместо Lattice, чтобы избежать коллизии с Mathlib.Order.Lattice
abbrev Grid (d N : ℕ) := Fin d → Fin N

abbrev GridField (d N : ℕ) := Grid d N → ℝ

/--
Отображение макроузла y и смещения ε ∈ {0, 1}^d в микроузел решётки 2N:
  x_μ = 2 * y_μ + ε_μ.
-/
def microSite (d N : ℕ) (y : Grid d N) (ε : Fin d → Fin 2) : Grid d (2 * N) :=
  fun μ => ⟨2 * (y μ).val + (ε μ).val, by
    have hy := (y μ).isLt
    have hε := (ε μ).isLt
    omega⟩

/--
Количество узлов в одном d-мерном блоке равно 2^d.
-/
lemma card_micro_block (d : ℕ) : Fintype.card (Fin d → Fin 2) = 2 ^ d := by
  simp [Fintype.card_fin]

/--
Алгебраическое тождество: (1/2)^d * 2^d = 1.
-/
lemma inv_two_pow_mul_two_pow_mul (d : ℕ) (M : ℝ) :
    ((1 / 2 : ℝ) ^ d) * (((2 : ℝ) ^ d) * M) = M := by
  have h_two : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  calc ((1 / 2 : ℝ) ^ d) * (((2 : ℝ) ^ d) * M)
    _ = (((1 / 2 : ℝ) ^ d) * ((2 : ℝ) ^ d)) * M := (mul_assoc _ _ _).symm
    _ = (((1 / 2 : ℝ) * 2) ^ d) * M := by rw [← mul_pow]
    _ = (1 ^ d) * M := by rw [h_two]
    _ = 1 * M := by rw [one_pow]
    _ = M := one_mul M

/--
**d-мерный оператор усреднения Каданова:**
  ϕ'(y) = (1 / 2^d) * ∑_{ε ∈ {0, 1}^d} ϕ(2y + ε).
-/
def kadanoffAverageD (d N : ℕ) (ϕ : GridField d (2 * N)) (y : Grid d N) : ℝ :=
  ((1 / 2 : ℝ) ^ d) * ∑ ε : Fin d → Fin 2, ϕ (microSite d N y ε)

/--
**Скейлинговая оценка для d-мерного блочного усреднения.**
-/
theorem kadanoffD_sup_bound (d N : ℕ) (ϕ : GridField d (2 * N)) (M : ℝ)
    (hM : ∀ j, |ϕ j| ≤ M) (y : Grid d N) :
    |kadanoffAverageD d N ϕ y| ≤ M := by
  dsimp [kadanoffAverageD]
  have h_pos : 0 < (1 / 2 : ℝ) ^ d := pow_pos (by norm_num) d
  rw [abs_mul, abs_of_pos h_pos]
  have h_abs_sum : |∑ ε : Fin d → Fin 2, ϕ (microSite d N y ε)| ≤
      ∑ ε : Fin d → Fin 2, |ϕ (microSite d N y ε)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_sum_le : ∑ ε : Fin d → Fin 2, |ϕ (microSite d N y ε)| ≤
      ∑ _ε : Fin d → Fin 2, M :=
    Finset.sum_le_sum (fun ε _ => hM _)
  have h_card : Fintype.card (Fin d → Fin 2) = 2 ^ d := card_micro_block d
  have h_sum_const : (∑ _ε : Fin d → Fin 2, M) = ((2 : ℝ) ^ d) * M := by
    rw [Finset.sum_const, Finset.card_univ, h_card, nsmul_eq_mul]
    push_cast
    rfl
  have h_block : |∑ ε : Fin d → Fin 2, ϕ (microSite d N y ε)| ≤ ((2 : ℝ) ^ d) * M :=
    h_abs_sum.trans (h_sum_le.trans (le_of_eq h_sum_const))
  have h_nonneg : 0 ≤ (1 / 2 : ℝ) ^ d := pow_nonneg (by norm_num) d
  have h_scaled := mul_le_mul_of_nonneg_left h_block h_nonneg
  exact h_scaled.trans (le_of_eq (inv_two_pow_mul_two_pow_mul d M))

/--
**d-мерный шаг РГ с ренормировкой поля (Wave-function Rescaling Z).**
-/
def kadanoffAverageWithRescaling
    (d N : ℕ) (Z : ℝ) (ϕ : GridField d (2 * N)) (y : Grid d N) : ℝ :=
  Z * kadanoffAverageD d N ϕ y

/--
**Скейлинговая оценка с масштабным множителем Z:**
  |ϕ'_Z(y)| ≤ |Z| * M.
-/
theorem kadanoffD_rescaled_bound (d N : ℕ) (Z : ℝ) (ϕ : GridField d (2 * N)) (M : ℝ)
    (hM : ∀ j, |ϕ j| ≤ M) (y : Grid d N) :
    |kadanoffAverageWithRescaling d N Z ϕ y| ≤ |Z| * M := by
  dsimp [kadanoffAverageWithRescaling]
  rw [abs_mul]
  have h_avg := kadanoffD_sup_bound d N ϕ M hM y
  exact mul_le_mul_of_nonneg_left h_avg (abs_nonneg Z)

end MultidimKadanoffGrid
