import Lake
open Lake DSL

package lean_metrics where

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib LeanMetrics where
  srcDir := "."
  roots := #[
    `Scaling,
    `AdvancedScaling,
    `Ising,
    `PolymerScaling,
    `CriticalScaling,
    `RigorousExtensions,
    `ThermodynamicStability,
    `ExactRenormalization,
    `TransferMatrixRG,
    `ThermodynamicLimit
  ]
