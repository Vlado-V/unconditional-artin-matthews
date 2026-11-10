module

public import ArtinMatthews.SpectralCuspContinuousRepresentative
public import ArtinMatthews.SpectralGamma0EisensteinIntegralExchange
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Above the extension height the literal horizontal mean is the actual
horocycle integral. This small generic adapter avoids unfolding ambient L2. -/
noncomputable section
open Set MeasureTheory
namespace ArtinMatthews

theorem cuspContinuousPlaneExtension_mean (w Y : ℝ) (hw : 0≤w) (hY : 0<Y)
    (F : UpperHalfPlane → ℂ) (y : ℝ) (hy : Y<y) :
    cuspHorizontalMean w (cuspContinuousPlaneExtension Y hY F) y=
      (w:ℂ)⁻¹*(∫ x in (0:ℝ)..w, F (gamma0EisensteinHorizontalPoint y (hY.trans hy) x)) := by
  unfold cuspHorizontalMean
  rw [← intervalIntegral.integral_of_le hw]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  exact cuspContinuousPlaneExtension_at_upper Y hY F
    (gamma0EisensteinHorizontalPoint y (hY.trans hy) x) hy.le

end ArtinMatthews
