import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Basic

noncomputable section

open BigOperators Finset

/-!
# Усиления и граничные тесты теории РГ, модели Изинга и скейлинга
-/

/-!
===============================================================================
УСИЛЕНИЕ 1: БЛОКИНГ КАДАНОВА ДЛЯ ПРОИЗВОЛЬНОГО МАСШТАБА L ≥ 1 В d ИЗМЕРЕНИЯХ
===============================================================================
-/

section GeneralizedKadanoff

abbrev Grid (d N : ℕ) := Fin d → Fin N
abbrev GridField (d N : ℕ) := Grid d N → ℝ

/--
Отображение макроузла y и смещения ε ∈ {0, ..., L-1}^d в микроузел решётки L * N:
x_μ = L * y_μ + ε_μ.
Корректность доказана через факторизацию L * (y + 1) ≤ L * N.
-/
def microSiteL (d N L : ℕ) (y : Grid d N) (ε : Fin d → Fin L) : Grid d (L * N) :=
  fun μ => ⟨L * (y μ).val + (ε μ).val, by
    have hy : (y μ).val + 1 ≤ N := (y μ).isLt
    have h1 : L * (y μ).val + L ≤ L * N := by
      calc L * (y μ).val + L = L * ((y μ).val + 1) := by ring
        _ ≤ L * N := Nat.mul_le_mul_left L hy
    have hε := (ε μ).isLt
    omega⟩

/-- Число микроузлов в d-мерном блоке со стороной L равно строго L^d -/
lemma card_micro_block_L (d L : ℕ) : Fintype.card (Fin d → Fin L) = L ^ d := by
  simp [Fintype.card_fin]

/-- Аналитическое сокращение объёма блока для произвольного L > 0 -/
lemma inv_L_pow_mul_L_pow (d L : ℕ) (hL : L ≠ 0) (M : ℝ) :
    ((1 / (L : ℝ)) ^ d) * (((L : ℝ) ^ d) * M) = M := by
  have hL_pos : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL
  have h_cancel : (1 / (L : ℝ)) * (L : ℝ) = 1 := one_div_mul_cancel hL_pos
  calc ((1 / (L : ℝ)) ^ d) * (((L : ℝ) ^ d) * M)
    _ = (((1 / (L : ℝ)) ^ d) * ((L : ℝ) ^ d)) * M := (mul_assoc _ _ _).symm
    _ = (((1 / (L : ℝ)) * (L : ℝ)) ^ d) * M := by rw [← mul_pow]
    _ = (1 ^ d) * M := by rw [h_cancel]
    _ = 1 * M := by rw [one_pow]
    _ = M := one_mul M

/-- Обобщённый оператор усреднения Каданова для произвольного масштаба L -/
def kadanoffAverageL (d N L : ℕ) (ϕ : GridField d (L * N)) (y : Grid d N) : ℝ :=
  ((1 / (L : ℝ)) ^ d) * ∑ ε : Fin d → Fin L, ϕ (microSiteL d N L y ε)

/--
**Главная обобщённая скейлинговая теорема Каданова:**
Для ЛЮБОГО размера решётки N, ЛЮБОЙ размерности d и ЛЮБОГО шага укрупнения L > 0:
флуктуации макрополя не превосходят флуктуаций микрополя: |ϕ'_L(y)| ≤ M.
-/
theorem kadanoffL_sup_bound (d N L : ℕ) (hL : 0 < L)
    (ϕ : GridField d (L * N)) (M : ℝ)
    (hM : ∀ j, |ϕ j| ≤ M) (y : Grid d N) :
    |kadanoffAverageL d N L ϕ y| ≤ M := by
  dsimp [kadanoffAverageL]
  have hL_ne : L ≠ 0 := by omega
  have h_pos : 0 < (1 / (L : ℝ)) ^ d := pow_pos (by positivity) d
  rw [abs_mul, abs_of_pos h_pos]
  have h_abs_sum : |∑ ε : Fin d → Fin L, ϕ (microSiteL d N L y ε)| ≤
      ∑ ε : Fin d → Fin L, |ϕ (microSiteL d N L y ε)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_sum_le : ∑ ε : Fin d → Fin L, |ϕ (microSiteL d N L y ε)| ≤
      ∑ _ε : Fin d → Fin L, M :=
    Finset.sum_le_sum (fun ε _ => hM _)
  have h_card : Fintype.card (Fin d → Fin L) = L ^ d := card_micro_block_L d L
  have h_sum_const : (∑ _ε : Fin d → Fin L, M) = ((L : ℝ) ^ d) * M := by
    rw [Finset.sum_const, Finset.card_univ, h_card, nsmul_eq_mul]
    push_cast
    rfl
  have h_block : |∑ ε : Fin d → Fin L, ϕ (microSiteL d N L y ε)| ≤ ((L : ℝ) ^ d) * M :=
    h_abs_sum.trans (h_sum_le.trans (le_of_eq h_sum_const))
  have h_nonneg : 0 ≤ (1 / (L : ℝ)) ^ d := pow_nonneg (by positivity) d
  have h_scaled := mul_le_mul_of_nonneg_left h_block h_nonneg
  exact h_scaled.trans (le_of_eq (inv_L_pow_mul_L_pow d L hL_ne M))

end GeneralizedKadanoff

/-!
===============================================================================
УСИЛЕНИЕ 2: ПОЛНАЯ Z₂-ДУАЛЬНОСТЬ И ТЕОРЕМА О ЗАНУЛЕНИИ НАМАГНИЧЕННОСТИ
===============================================================================
-/

section IsingStrictSymmetry

inductive Spin | up | down deriving DecidableEq

def Spin.val : Spin → ℝ
  | up => 1
  | down => -1

def Spin.flip : Spin → Spin
  | up => down
  | down => up

@[simp] lemma val_flip (s : Spin) : (Spin.flip s).val = - s.val := by
  cases s <;> [rfl; (dsimp [Spin.flip, Spin.val]; ring)]

@[simp] lemma flip_involutive (s : Spin) : Spin.flip (Spin.flip s) = s := by
  cases s <;> rfl

instance : Fintype Spin where
  elems := {Spin.up, Spin.down}
  complete := by intro s; cases s <;> simp

abbrev Config (V : Type*) := V → Spin

def flipConfig {V : Type*} (σ : Config V) : Config V :=
  fun i => Spin.flip (σ i)

@[simp] lemma flipConfig_flipConfig {V : Type*} (σ : Config V) :
    flipConfig (flipConfig σ) = σ := by
  funext i; exact flip_involutive (σ i)

def flipEquiv (V : Type*) : Config V ≃ Config V where
  toFun := flipConfig
  invFun := flipConfig
  left_inv := flipConfig_flipConfig
  right_inv := flipConfig_flipConfig

variable {V : Type*} [Fintype V]

def isingH (J : V → V → ℝ) (h : ℝ) (σ : Config V) : ℝ :=
  - (1 / 2 : ℝ) * (∑ i : V, ∑ j : V, J i j * (σ i).val * (σ j).val) -
  h * (∑ i : V, (σ i).val)

def totalMag (σ : Config V) : ℝ :=
  ∑ i : V, (σ i).val

lemma totalMag_flip (σ : Config V) : totalMag (flipConfig σ) = - totalMag σ := by
  dsimp [totalMag, flipConfig]
  rw [← Finset.sum_neg_distrib]
  simp_rw [val_flip]

/--
**Расширенная Z₂-дуальность Гамильтониана во внешнем поле:**
H(-σ, -h) = H(σ, h).
-/
theorem hamiltonian_extended_duality (J : V → V → ℝ) (h : ℝ) (σ : Config V) :
    isingH J (-h) (flipConfig σ) = isingH J h σ := by
  dsimp [isingH, flipConfig]
  have h_pair : ∀ i j : V,
      J i j * (Spin.flip (σ i)).val * (Spin.flip (σ j)).val =
      J i j * (σ i).val * (σ j).val := by
    intro i j; rw [val_flip, val_flip]; ring
  have h_field : (-h) * ∑ i : V, (Spin.flip (σ i)).val = h * ∑ i : V, (σ i).val := by
    simp_rw [val_flip]
    rw [Finset.sum_neg_distrib]
    ring
  simp_rw [h_pair]
  rw [h_field]

variable [DecidableEq V]

/--
**Фундаментальная теорема о занулении спонтанной намагниченности:**
В нулевом внешнем поле (h = 0) в конечном объёме средняя намагниченность строго равна нулю:
  ∑_σ M(σ) * exp(-β H(σ)) = 0.
-/
theorem zero_spontaneous_magnetization (J : V → V → ℝ) (β : ℝ) :
    (∑ σ : Config V, totalMag σ * Real.exp (-β * isingH J 0 σ)) = 0 := by
  have h_symm : ∀ σ, isingH J 0 (flipConfig σ) = isingH J 0 σ := by
    intro σ
    have h := hamiltonian_extended_duality J 0 σ
    rw [neg_zero] at h
    exact h
  let F : Config V → ℝ := fun σ => totalMag σ * Real.exp (-β * isingH J 0 σ)
  have h_odd : ∀ σ, F (flipConfig σ) = - F σ := by
    intro σ
    dsimp [F]
    rw [totalMag_flip, h_symm]
    ring
  have h_sum_equiv : (∑ σ : Config V, F σ) = (∑ σ : Config V, F (flipConfig σ)) := by
    exact (Equiv.sum_comp (flipEquiv V) F).symm
  have h_neg : (∑ σ : Config V, F (flipConfig σ)) = - (∑ σ : Config V, F σ) := by
    simp only [h_odd, Finset.sum_neg_distrib]
  linarith

end IsingStrictSymmetry

/-!
===============================================================================
УСИЛЕНИЕ 3: ТЕСТ МИНИМАЛЬНОЙ ГРАНИЦЫ d = 1 ДЛЯ ПОЛИМЕРОВ
===============================================================================
-/

section BoundaryDimensionPolymers

def floryNu (d : ℕ) : ℝ :=
  if d ≤ 4 then 3 / ((d : ℝ) + 2) else 1 / 2

/--
**Тест минимальной границы d = 1:**
В 1D цепь вытягивается в абсолютно прямой жесткий стержень (ν = 1).
-/
theorem polymer_boundary_1d_rigid_rod : floryNu 1 = 1 := by
  dsimp [floryNu]
  norm_num

/-- Монотонность: в 1D клубок более вытянут, чем в 2D, а в 2D — больше, чем в 3D -/
theorem polymer_swelling_monotonicity :
    floryNu 3 < floryNu 2 ∧ floryNu 2 < floryNu 1 := by
  dsimp [floryNu]
  exact ⟨by norm_num, by norm_num⟩

end BoundaryDimensionPolymers

/-!
===============================================================================
УСИЛЕНИЕ 4: ПЕРИОДИЧЕСКИЕ ГРАНИЧНЫЕ УСЛОВИЯ (ТОР ℤ_N) И ТРАНСЛЯЦИИ
===============================================================================
-/

section PeriodicBoundaryConditions

variable (N : ℕ)

/-- Сдвиг на торе ℤ_N: x ↦ x + 1 -/
def torusShift (i : ZMod N) : ZMod N := i + 1

/-- Обратный сдвиг на торе ℤ_N: x ↦ x - 1 -/
def torusUnshift (i : ZMod N) : ZMod N := i - 1

lemma torusShift_torusUnshift (i : ZMod N) : torusShift N (torusUnshift N i) = i := by
  dsimp [torusShift, torusUnshift]
  ring

lemma torusUnshift_torusShift (i : ZMod N) : torusUnshift N (torusShift N i) = i := by
  dsimp [torusShift, torusUnshift]
  ring

/-- Биекция циклического сдвига на торе ℤ_N (трансляционная группа) -/
def torusEquiv : ZMod N ≃ ZMod N where
  toFun := torusShift N
  invFun := torusUnshift N
  left_inv := torusUnshift_torusShift N
  right_inv := torusShift_torusUnshift N

/-- Гамильтониан 1D кольца Изинга с периодическими граничными условиями (ПГУ) на ℤ_N -/
def isingRingH [NeZero N] (J : ℝ) (σ : ZMod N → ℝ) : ℝ :=
  - J * (∑ i : ZMod N, σ i * σ (torusShift N i))

/--
**Теорема о трансляционной инвариантности кольца Изинга:**
При циклическом сдвиге всей конфигурации вдоль тора σ'(i) = σ(i + 1) энергия строго сохраняется.
-/
theorem ising_ring_translational_invariance [NeZero N] (J : ℝ) (σ : ZMod N → ℝ) :
    isingRingH N J (fun i => σ (torusShift N i)) = isingRingH N J σ := by
  dsimp [isingRingH]
  have h_sum : (∑ i : ZMod N, σ (torusShift N i) * σ (torusShift N (torusShift N i))) =
               (∑ i : ZMod N, σ i * σ (torusShift N i)) := by
    exact Equiv.sum_comp (torusEquiv N) (fun i => σ i * σ (torusShift N i))
  rw [h_sum]

end PeriodicBoundaryConditions
