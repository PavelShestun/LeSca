import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import DefectLadder

namespace Certifier

structure LadderCertificate where
  K_par : Float
  K_perp : Float
  lambda1 : Float
  lambda2 : Float
  lambda3 : Float
  spectral_gap : Float
  target_epsilon : Float
  certified_N_star : Nat
deriving Repr

def computeSpectralParams (K_par K_perp : Float) : Float × Float × Float × Float :=
  let s_perp := Float.sinh K_perp
  let c_perp := Float.cosh K_perp
  let s_par := Float.sinh (2.0 * K_par)
  let c_par := Float.cosh (2.0 * K_par)
  let discr := s_perp * s_perp * c_par * c_par + 1.0
  let l1 := 2.0 * c_perp * c_par + 2.0 * Float.sqrt discr
  let l2 := 2.0 * Float.exp K_perp * s_par
  let l3 := 2.0 * Float.exp (-K_perp) * s_par
  let gap := 1.0 - (l2 / l1)
  (l1, l2, l3, gap)

def computeCertifiedNStar (l1 l2 : Float) (eps : Float) : Nat :=
  let ratio := l2 / l1
  if ratio >= 1.0 || ratio <= 0.0 then 2
  else
    let numerator := Float.log (3.0 / eps)
    let denominator := Float.log (1.0 / ratio)
    let n_float := numerator / denominator
    let n_int := n_float.toUInt64.toNat
    if n_int % 2 == 1 then n_int + 1 else n_int

def generateCertificate (K_par K_perp eps : Float) : LadderCertificate :=
  let (l1, l2, l3, gap) := computeSpectralParams K_par K_perp
  let n_star := computeCertifiedNStar l1 l2 eps
  { K_par := K_par,
    K_perp := K_perp,
    lambda1 := l1,
    lambda2 := l2,
    lambda3 := l3,
    spectral_gap := gap,
    target_epsilon := eps,
    certified_N_star := n_star }

end Certifier
