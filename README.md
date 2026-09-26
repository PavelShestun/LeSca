# LeSca: Formal Renormalization Group, Critical Phenomena & Scaling Theory in Lean 4

![Lean 4](https://img.shields.io/badge/Lean-4.35-blue.svg)
![Mathlib 4](https://img.shields.io/badge/Mathlib-4-purple.svg)
![Verification](https://img.shields.io/badge/Verification-100%25%20No%20Sorry-success.svg)
![Warnings](https://img.shields.io/badge/Warnings-0-brightgreen.svg)
![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)

**LeSca** (*Lean Scaling & Renormalization Group*) — первая всеобъемлющая строго верифицированная библиотека теории ренормализационной группы (РГ), критических явлений и скейлингового анализа на интерактивном доказателе теорем Lean 4.

Охватывая **8 полностью верифицированных модулей** с нулевым числом нерешённых целей (`sorry`) и нулевым числом предупреждений компилятора, библиотека объединяет микроскопическую физику дискретных решёток, взятие частичного следа в статистических суммах, непрерывные динамические траектории потока Вильсона — Фишера, де Женновский класс полимеров ($n \to 0$) и вывод универсальных термодинамических законов скейлинга Видома.

---

## 🗺️ Архитектурная карта модулей

```
                           [ Renormalization Group Theory ]
                                          │
            ┌─────────────────────────────┴─────────────────────────────┐
            ▼                                                           ▼
   RG Dynamics & Contraction                                Microscopic & Field Models
─────────────────────────────────                         ─────────────────────────────────
1. Scaling.lean:                                          3. Ising.lean (n = 1):
   • Сжатие нормы ‖Tⁿ(v)‖ ≤ ρⁿ‖v‖                            • Дискретные спины & ℤ₂-инвариантность
   • Эволюция собственных мод T(v) = s • v                   • Положительность статсуммы Z > 0
                                                             • Сжатие децимации T(K) < K
2. AdvancedScaling.lean:                                                │
   • Асимптотика O(ρⁿ) (IsBigO / atTop)                                 ▼ (предел де Женна n → 0)
   • Локальная устойчивость нелинейных потоков            4. PolymerScaling.lean (n = 0):
   • d-мерный блочный спин Каданова                          • Показатель Флори ν(d, solvent)
                                                             • Верхняя критическая размерность d_c = 4
6. RigorousExtensions.lean:                                  • Иерархия фаз: Poor < Theta < Good
   • Каданов для произвольного шага L ≥ 1                    • Вариационный баланс свободной энергии
   • Зануление намагниченности ⟨M⟩ = 0 (h=0)                            │
   • ПГУ на торе ℤ_N и трансляционная инвариантность                    │
            │                                                           │
            └─────────────────────────────┬─────────────────────────────┘
                                          ▼
                      Universal Scaling & Exact Foundations
                    ─────────────────────────────────────────
                    5. CriticalScaling.lean:
                       • Законы Рашбрука, Видома, Фишера и Джозефсона
                       • Согласование с точным решением Онзагера (2D)
                       • Критерий Гинзбурга: 2 - α = dν ↔ d = 4

                    7. ThermodynamicStability.lean:
                       • Ограниченность наблюдаемых |⟨X⟩| ≤ M
                       • Неотрицательность восприимчивости χ ≥ 0
                       • Корни бета-функции β(g) и устойчивость WF

                    8. ExactRenormalization.lean [НОВОЕ ЯДРО]:
                       • Тождество децимации: ∑_{s₂} e^{-H} = C₀ e^{-H'}
                       • Точное сохранение статсуммы: Z₃(K) = C₀(K) Z₂(K')
                       • Аналитическая траектория g(ℓ) и релаксация к WF
                       • Вывод скейлингового анзаца Видома f = t^(d/y_t) Φ
```

---

## 📚 Обзор модулей и ключевых теорем

### 1. `ExactRenormalization.lean` — Микроскопический вывод и динамика потока
Закрывает фундаментальный мост между микроскопическим статистическим усреднением и непрерывной динамикой потока:
* `microscopic_decimation_identity`: Строгое доказательство сворачивания взаимодействия при взятии частичного следа по промежуточному спину $s_2 \in \{\pm 1\}$:
  $$\sum_{s_2} e^{K s_2 (s_1 + s_3)} = C_0(K) \, e^{K' s_1 s_3}, \quad K' = \frac{1}{2} \ln \cosh(2K), \quad C_0(K) = 2 \sqrt{\cosh(2K)}$$
* `partition_function_exact_decimation`: Теорема сохранения статсуммы при РГ-шаге: $Z_3(K) = C_0(K) Z_2(K')$.
* `wf_initial_condition` & `wf_fixed_point_invariant`: Проверка начального условия $g(0) = g_0$ и стационарности неподвижной точки $g^* = \varepsilon / b$ для непрерывной траектории потока Вильсона — Фишера.
* `wf_approach_rate`: Точная аналитическая скорость релаксации возмущения $|g(\ell) - g^*| \sim e^{-\varepsilon \ell}$, связывающая показатель затухания с $\varepsilon = 4 - d$.
* `widom_scaling_function_derivation`: Строгий вывод универсального скейлингового анзаца Видома $f(t, h) = t^{d / y_t} \Phi(h / t^\Delta)$ из инвариантности свободной энергии относительно масштабного фактора $b = t^{-1/y_t}$.

### 2. `Scaling.lean` — Дискретная динамика РГ
* `rg_scaling_bound`: Мультимасштабное сжатие: $\|T(w)\| \le \rho \|w\| \implies \|T^n(w)\| \le \rho^n \|w\|$.
* `rgFlow_eigen`: Точная эволюция собственных операторов: $T(v) = s \cdot v \implies T^n(v) = s^n \cdot v$.
* `concreteToyRG`: Конкретная одномерная верифицированная модель децимации на $\mathbb{R}$.

### 3. `AdvancedScaling.lean` — Нелинейные потоки и $d$-мерная геометрия
* `rg_isBigO`: Связь потока с фильтрами асимптотического анализа Mathlib: $(T^n v) = O(\rho^n)$ при $n \to \infty$ (`Filter.atTop`).
* `nonlinear_rg_scaling`: Локальная устойчивость гауссовой неподвижной точки при квадратичных возмущениях $\|T(w)\| \le \rho \|w\| + C \|w\|^2$.
* `kadanoffD_sup_bound`: Усреднение по блоку на торе $(\mathbb{Z} / 2N\mathbb{Z})^d$ с точным сокращением объёма $(1/2)^d \cdot 2^d = 1$.
* `kadanoffD_rescaled_bound`: Перенормировка волновой функции поля $Z$ (Wave-function rescaling).

### 4. `Ising.lean` — Микрофизика модели Изинга ($n = 1$)
* `hamiltonian_spin_flip_symmetry`: Спин-флип симметрия $\mathbb{Z}_2$: $H(-\sigma) = H(\sigma)$ при $h = 0$.
* `partitionFunction_pos`: Строгая положительность статсуммы $Z > 0$.
* `gibbsWeight_normalized`: Точная нормировка меры Гиббса: $\sum_\sigma P(\sigma) = 1$.
* `ising_decimation_contraction`: Монотонное сжатие связи в 1D: $T(K) < K$, подтверждающее отсутствие дальнего порядка при $T > 0$.

### 5. `PolymerScaling.lean` — Класс универсальности де Женна ($n \to 0$)
* `upper_critical_dimension_crossover`: Доказательство кроссовера в гауссово поведение при $d_c = 4$: $\nu(4, \text{Good}) = 1/2$.
* `solvent_phase_hierarchy_3d`: Иерархия фаз растворителя в 3D: $\nu_{\text{Poor}} < \nu_{\text{Theta}} < \nu_{\text{Good}} \iff 1/3 < 1/2 < 3/5$.
* `flory_scaling_exponent_balance`: Вариационный вывод Флори: баланс упругости $R^2/N$ и исключённого объёма $N^2/R^d$ даёт $\nu = 3 / (d + 2)$.

### 6. `CriticalScaling.lean` — Универсальные законы подобия
* `rushbrooke_scaling`: Закон Рашбрука $\alpha + 2\beta + \gamma = 2$.
* `fisher_scaling`: Закон Фишера $\gamma = \nu(2 - \eta)$.
* `josephson_hyperscaling`: Гиперскейлинг Джозефсона $2 - \alpha = d\nu$.
* `widom_scaling`: Закон Видома $\gamma = \beta(\delta - 1)$.
* `onsager_matches_RG`: Точное совпадение с решением Онзагера 1944 года для 2D Изинга ($y_t = 1$, $y_h = 15/8$).
* `mean_field_hyperscaling_iff_four`: Критерий Гинзбурга: среднее поле подчиняется гиперскейлингу $\iff d = 4$.

### 7. `RigorousExtensions.lean` — Обобщения и граничные тесты
* `kadanoffL_sup_bound`: Блокинг Каданова для произвольного масштаба $L \ge 1$ с объёмом блока $L^d$.
* `zero_spontaneous_magnetization`: Доказательство отсутствия спонтанной намагниченности в конечном объёме при $h = 0$ через биекцию `flipEquiv`.
* `polymer_boundary_1d_rigid_rod`: Предел жёсткого стержня в 1D: $\nu(1) = 1$.
* `ising_ring_translational_invariance`: Инвариантность энергии относительно сдвигов на кольце $\mathbb{Z}_N$.

### 8. `ThermodynamicStability.lean` — Термодинамика и непрерывная РГ
* `gibbsExpectation_bound`: Универсальное ограничение на среднее: $|\langle X \rangle| \le \max |X|$.
* `twoPoint_correlation_bounded`: Насыщение коррелятора: $|\langle \sigma_i \sigma_j \rangle| \le 1$.
* `thermodynamic_stability_susceptibility_nonneg`: Устойчивость: $\operatorname{Var}(M) \ge 0 \implies \chi \ge 0$.
* `wilson_fisher_fixed_points`: Классификация корней $\beta(g) = 0$ на $g^* = 0$ (Гаусс) и $g^* = \varepsilon / b$ (Вильсон — Фишер).
* `wilson_fisher_ir_stable`: Теорема об инфракрасном аттракторе: $\beta'(\varepsilon / b) = +\varepsilon > 0$.

---

## 🛠️ Сборка и верификация

### Требования
* Установленный Lean version manager (`elan`).

### Клонирование и проверка доказательств
```bash
git clone git@github.com:PavelShestun/LeSca.git
cd LeSca

# Загрузка предкомпилированного кэша Mathlib 4 (быстрый старт)
lake exe cache get

# Сборка и полная проверка всех 8 модулей
lake build
```

Компилятор Lean верифицирует 100% доказательств без использования аксиомы `sorry` и с 0 предупреждений.

---

## 📖 Ключевые публикации

1. **L. P. Kadanoff** (1966), *Scaling laws for Ising models near $T_c$*, Physics Physique Fizika 2, 263.
2. **K. G. Wilson** (1971), *Renormalization Group and Critical Phenomena*, Phys. Rev. B 4, 3174 (Нобелевская премия 1982).
3. **K. G. Wilson & M. E. Fisher** (1972), *Critical Exponents in 3.99 Dimensions*, Phys. Rev. Lett. 28, 240.
4. **P.-G. de Gennes** (1972), *Exponents for the polymer problem as a $n \to 0$ limit of the vector model*, Phys. Lett. A 38, 339 (Нобелевская премия 1991).
5. **L. Onsager** (1944), *Crystal Statistics. I. A Two-Dimensional Model with an Order-Disorder Transition*, Phys. Rev. 65, 117.

---

## 📄 Лицензия

Проект распространяется под открытой лицензией [MIT](LICENSE).
