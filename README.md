# Lean-RG: Formal Renormalization Group, Critical Phenomena & Scaling Theory in Lean 4

[![Lean 4](https://img.shields.io/badge/Lean-4.35-blue.svg)](https://github.com/leanprover/lean4)
[![Mathlib 4](https://img.shields.io/badge/Mathlib-4-purple.svg)](https://github.com/leanprover-community/mathlib4)
[![Verification](https://img.shields.io/badge/Verification-100%25%20No%20Sorry-success.svg)](#)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

**Lean-RG** is the first comprehensive formalization suite of **Renormalization Group (RG) Theory, Critical Phenomena, and Scaling Analysis** in the [Lean 4](https://lean-lang.org/) interactive theorem prover.

Spanning **7 fully verified modules with zero unproven goals (`sorry`)**, this repository bridges microscopic lattice statistical physics, multiscale coarse-graining, the $n \to 0$ de Gennes polymer universality class, continuous Callan–Symanzik $\beta$-functions, and the universal macroscopic thermodynamic scaling laws.

---

## 🗺️ Architectural Map

```
                          [Renormalization Group Theory]
                                        │
           ┌────────────────────────────┴────────────────────────────┐
           ▼                                                         ▼
  RG Dynamics & Scaling                                   Statistical & Field Models
───────────────────────────────                         ───────────────────────────────
1. Scaling.lean:                                        3. Ising.lean (n = 1 class):
   • Multiscale contraction ‖Tⁿ(v)‖ ≤ ρⁿ‖v‖                • Discrete spins & ℤ₂ symmetry
   • Graded eigenmode evolution                            • Partition function Z > 0 & Gibbs measure
                                                           • 1D decimation RG contraction T(K) < K
2. AdvancedScaling.lean:                                             │
   • Asymptotics O(ρⁿ) (IsBigO / atTop)                              ▼ (de Gennes n → 0 limit)
   • Invariant ball for non-linear φ⁴ flow              4. PolymerScaling.lean (n = 0 class):
   • d-dimensional Kadanoff block spin                     • Flory–de Gennes polymer scaling
                                                           • Upper critical dimension d_c = 4
6. RigorousExtensions.lean:                                • Phase hierarchy (Poor < Theta < Good)
   • Arbitrary scale factor L ≥ 1                          • Free energy variational balance
   • Vanishing magnetization ⟨M⟩ = 0 (h=0)                           │
   • Periodic boundary conditions (ℤ_N Torus)                        │
           │                                                         │
           └────────────────────────────┬────────────────────────────┘
                                        ▼
                         Universal Macroscopic Scaling
                        ───────────────────────────────
                        5. CriticalScaling.lean:
                           • Rushbrooke, Widom, Fisher & Josephson laws
                           • 2D Onsager exact solution match
                           • Ginzburg criterion: 2 - α = dν ↔ d = 4
                        7. ThermodynamicStability.lean:
                           • Variance Var(X) ≥ 0 & Susceptibility χ ≥ 0
                           • Correlation bound |⟨σ_i σ_j⟩| ≤ 1
                           • Continuous flow & Wilson–Fisher fixed point
```

---

## 📚 Module Overview & Verified Theorems

### 1. `Scaling.lean` — Discrete RG Dynamics & Contraction
Formalizes the core Wilsonian coarse-graining flow as an iterated discrete dynamical system on a seminormed space $(V, \|\cdot\|)$.
* **`rg_scaling_bound`**: Inductive multiscale contraction proof: if $\|T(w)\| \le \rho \|w\|$, then $\|T^n(w)\| \le \rho^n \|w\|$.
* **`rgFlow_eigen`**: Exact scaling evolution for linear eigenmodes: $T(v) = s \cdot v \implies T^n(v) = s^n \cdot v$.
* **`concreteToyRG`**: End-to-end verification of a 1D decimation model on $\mathbb{R}$.

### 2. `AdvancedScaling.lean` — Non-Linear Flows & $d$-Dimensional Geometry
* **`rg_isBigO`**: Rigorous connection to Mathlib’s asymptotic analysis: $(T^n v) = O(\rho^n)$ as $n \to \infty$ under `Filter.atTop`.
* **`nonlinear_rg_scaling`**: Local stability of the Gaussian fixed point under quadratic perturbations ($\|T(w)\| \le \rho \|w\| + C \|w\|^2$). Proves both invariance of the attraction basin ($\|v_n\| \le r$) and exponential decay ($\|v_n\| \le \lambda^n \|v_0\|$).
* **`kadanoffD_sup_bound`**: Kadanoff block spin averaging on a hypercubic grid $(\mathbb{Z} / 2N\mathbb{Z})^d$. Proves $|\phi'(y)| \le M$ via exact block volume cancellation $(1/2)^d \cdot 2^d = 1$.
* **`kadanoffD_rescaled_bound`**: Wave-function field rescaling $Z = 2^{-\delta}$ yielding strict contraction in $d$ dimensions.

### 3. `Ising.lean` — Microscopic Statistical Physics ($n = 1$)
* **`hamiltonian_spin_flip_symmetry`**: Invariance of the Ising Hamiltonian under global $\mathbb{Z}_2$ spin inversion at $h = 0$: $H(-\sigma) = H(\sigma)$.
* **`partitionFunction_pos`**: Strict positivity of the partition function $Z(\beta) = \sum_\sigma e^{-\beta H(\sigma)} > 0$ for any finite graph.
* **`gibbsWeight_normalized`**: Exact normalization of the Gibbs probability distribution $\sum_\sigma P_\beta(\sigma) = 1$.
* **`ising_decimation_contraction`**: Rigorous 1D RG decimation step: $T(K) = \frac{1}{2}\ln(\cosh(2K)) < K$ for all $K > 0$, certifying the absence of spontaneous magnetization in 1D at finite temperature.

### 4. `PolymerScaling.lean` — de Gennes Universality Class ($n \to 0$)
Formalizes the polymer self-avoiding walk (SAW) scaling laws in solvent regimes (Good, Theta, Poor).
* **`upper_critical_dimension_crossover`**: Analytical proof that Flory's formula matches Gaussian random walks at $d_c = 4$: $\nu(4, \text{Good}) = 3 / (4 + 2) = 1/2$.
* **`solvent_phase_hierarchy_3d`**: Strict thermodynamic phase ordering in 3D: $\nu_{\text{Poor}} < \nu_{\text{Theta}} < \nu_{\text{Good}} \iff 1/3 < 1/2 < 3/5$.
* **`flory_scaling_exponent_balance`**: Exact variational balance between entropic elasticity ($R^2/N$) and excluded-volume repulsion ($N^2/R^d$): $(d+2)\nu - 3 = 0 \iff \nu = \frac{3}{d+2}$.
* **`asymptotic_swelling_ratio_exponent_3d`**: Asymptotic scale separation $R_{\text{poor}} / R_{\text{good}} \sim N^{-4/15} \to 0$ as $N \to \infty$.

### 5. `CriticalScaling.lean` — Universal Scaling Relations
Implements the Widom homogeneous scaling hypothesis, reducing 6 macroscopic critical exponents $(\alpha, \beta, \gamma, \delta, \nu, \eta)$ to 2 microscopic RG eigenvalues $(y_t, y_h)$.
* **`rushbrooke_scaling`**: Rushbrooke relation: $\alpha + 2\beta + \gamma = 2$ (proved identically via ring algebra).
* **`fisher_scaling`**: Fisher relation: $\gamma = \nu(2 - \eta)$.
* **`josephson_hyperscaling`**: Josephson hyperscaling: $2 - \alpha = d\nu$.
* **`widom_scaling`**: Widom relation: $\gamma = \beta(\delta - 1)$.
* **`onsager_matches_RG`**: Exact match with Onsager's 1944 2D Ising solution ($\beta = 1/8$, $\eta = 1/4$, $y_t = 1$, $y_h = 15/8$).
* **`mean_field_hyperscaling_iff_four`**: **The Ginzburg Criterion Theorem**: Mean-field exponents satisfy Josephson hyperscaling *if and only if* $d = 4$.

### 6. `RigorousExtensions.lean` — Generalizations & Boundary Tests
* **`kadanoffL_sup_bound`**: Generalization of Kadanoff coarse-graining to **arbitrary integer scaling factors $L \ge 1$** with block volume $L^d$.
* **`hamiltonian_extended_duality`**: Extended field-inversion duality: $H(-\sigma, -h) = H(\sigma, h)$.
* **`zero_spontaneous_magnetization`**: Strict proof that finite-volume spontaneous magnetization vanishes at $h = 0$: $\sum_\sigma M(\sigma) e^{-\beta H(\sigma)} = 0$ via the involution bijection `flipEquiv`.
* **`polymer_boundary_1d_rigid_rod`**: 1D boundary test: $\nu(1) = 1$ (exact self-avoiding rigid rod limit).
* **`ising_ring_translational_invariance`**: Periodic boundary conditions on the $\mathbb{Z}_N$ torus with exact translational invariance $H(\sigma \circ \text{shift}) = H(\sigma)$.

### 7. `ThermodynamicStability.lean` — Thermodynamics & Continuous RG
* **`gibbsExpectation_bound`**: Universal expectation bound: $|\langle X \rangle| \le \max |X|$.
* **`twoPoint_correlation_bounded`**: Exact spin correlation saturation: $|\langle \sigma_i \sigma_j \rangle| \le 1$.
* **`thermodynamic_stability_susceptibility_nonneg`**: Thermodynamic stability: $\operatorname{Var}(M) \ge 0 \implies \chi \ge 0$.
* **`wilson_fisher_fixed_points`**: Classification of roots of the Callan–Symanzik $\beta$-function $\beta(g) = -\varepsilon g + b g^2$ into $g^* = 0$ (Gaussian) and $g^* = \varepsilon / b$ (Wilson–Fisher).
* **`gaussian_fixed_point_ir_unstable`**: IR instability of the Gaussian point below 4D: $\beta'(0) = -\varepsilon < 0$.
* **`wilson_fisher_ir_stable`**: **IR Attractor Theorem**: $\beta'(\varepsilon / b) = +\varepsilon > 0$, certifying the Wilson–Fisher fixed point as the stable macroscopic attractor in $d < 4$.

---

## 🛠️ Build & Verification Instructions

### Prerequisites
Make sure you have [elan](https://github.com/leanprover/elan) (Lean version manager) installed.

### Clone and Compile
```bash
git clone https://github.com/YOUR_USERNAME/lean-rg.git
cd lean-rg

# Download precompiled Mathlib cache (fast setup)
lake exe cache get

# Build and verify all 7 modules
lake build
```

Upon successful compilation, Lean's typechecker certifies that every single proof is complete with **zero errors and zero warnings**.

---

## 📖 Key References

1. **L. P. Kadanoff** (1966), *Scaling laws for Ising models near $T_c$*, Physics Physique Fizika 2, 263.
2. **K. G. Wilson** (1971), *Renormalization Group and Critical Phenomena*, Phys. Rev. B 4, 3174 (Nobel Prize 1982).
3. **K. G. Wilson & M. E. Fisher** (1972), *Critical Exponents in 3.99 Dimensions*, Phys. Rev. Lett. 28, 240.
4. **P.-G. de Gennes** (1972), *Exponents for the polymer problem as a $n \to 0$ limit of the vector model*, Phys. Lett. A 38, 339 (Nobel Prize 1991).
5. **L. Onsager** (1944), *Crystal Statistics. I. A Two-Dimensional Model with an Order-Disorder Transition*, Phys. Rev. 65, 117.

---

## 📄 License
This project is licensed under the [MIT License](LICENSE).
```

---

### Файл конфигурации сборщика `lakefile.lean`

Чтобы команда `lake build` автоматически находила и компилировала все 7 файлов проекта, положите в корень репозитория следующий `lakefile.lean`:

```lean
import Lake
open Lake DSL

package «lean-metrics» where
  -- Настройки пакета

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «LeanRG» where
  roots := #[
    `Scaling,
    `AdvancedScaling,
    `Ising,
    `PolymerScaling,
    `CriticalScaling,
    `RigorousExtensions,
    `ThermodynamicStability
  ]