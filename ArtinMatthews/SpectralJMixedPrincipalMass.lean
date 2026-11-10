module

public import ArtinMatthews.SpectralJPrincipalMass
public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralMixedCuspPrincipalCutoff
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
open scoped MatrixGroups
noncomputable section

theorem gamma0MixedCusp_nativePrincipal_summable
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (hsmall : Y < (1 / 16) / (|cuspFourierFrequency 1 n| /
      (gamma0CuspTrueWidth (r * s) (gamma0CuspOneOver s) : ℝ))) :
    Summable (fun i : Gamma0HeatPrincipalCuspidalIndex (r * s) =>
      gamma0NativePrincipalDensity (r * s) (gamma0CuspOneOver s) Y hY n hn i /
        (1 + |gamma0CuspPrincipalParameter (r * s) i.val|) ^ 4) := by
  obtain ⟨C, hC, hBound⟩ := gamma0MixedCusp_principal_cutoff_orbit_bessel
  let B := |cuspFourierFrequency 1 n|
  let D := C * (1 + B / ((r * s : ℕ) : ℝ))
  apply gamma0NativePrincipalDensity_summable_of_moment (r * s)
    (gamma0CuspOneOver s) Y hY n hn D (by dsimp only [D, B]; positivity)
  intro u R hR hprincipal hcap
  have h := hBound r s hcop u n hn hR hY hsmall hprincipal hcap
  apply h.trans
  have hq : 0 ≤ B / ((r * s : ℕ) : ℝ) := by dsimp only [B]; positivity
  have hR₂ : R ≤ R ^ 2 := by nlinarith only [hR]
  have hmul := mul_le_mul_of_nonneg_left hR₂ hq
  dsimp only [D, B]
  have hquad : R ^ 2 + B * R / ((r * s : ℕ) : ℝ) ≤
      (1 + B / ((r * s : ℕ) : ℝ)) * R ^ 2 := by
    rw [show B * R / ((r * s : ℕ) : ℝ) = (B / ((r * s : ℕ) : ℝ)) * R by ring]
    nlinarith only [hmul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hquad hC.le

end
end ArtinMatthews
