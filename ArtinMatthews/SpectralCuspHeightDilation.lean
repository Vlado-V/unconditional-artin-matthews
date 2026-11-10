module

public import ArtinMatthews.SpectralCuspDiagonalFourierIntegral
public import ArtinMatthews.SpectralKLPhysicalDilation
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
open Set MeasureTheory
noncomputable section

/-- Exact cancellation of the two square-root factors against the width and height density. -/
theorem cuspFourierHeightPairing_scaled_integrand {y w : ℝ}
    (hy : 0 < y) (hw : 0 < w) (a b : ℝ) :
    w * ((Real.sqrt (y / w) * a) * (Real.sqrt (y / w) * b) / y ^ 2) = a * b / y := by
  have hs : Real.sqrt (y / w) ^ 2 = y / w := Real.sq_sqrt (div_nonneg hy.le hw.le)
  calc
    _ = w * (Real.sqrt (y / w) ^ 2 * a * b / y ^ 2) := by ring
    _ = _ := by
      rw [hs]
      field_simp [hy.ne', hw.ne']

/-- The literal rescaled cusp height pairing is the physical dx/x pairing. -/
theorem cuspFourierHeightPairing_dilation (q w : ℝ) (hq : 0 < q) (hw : 0 < w)
    (f g : ℝ → ℝ) :
    w * cuspFourierHeightPairing
      (fun y => Real.sqrt (y / w) * f ((q / w) * y))
      (fun y => Real.sqrt (y / w) * g ((q / w) * y)) =
        ∫ x in Ioi (0 : ℝ), f x * g x / x := by
  calc
    _ = ∫ y in Ioi (0 : ℝ), f (y / (w / q)) * g (y / (w / q)) / y := by
      unfold cuspFourierHeightPairing
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      change w * ((Real.sqrt (y / w) * f ((q / w) * y)) *
        (Real.sqrt (y / w) * g ((q / w) * y)) / y ^ 2) =
          f (y / (w / q)) * g (y / (w / q)) / y
      have ha : y / (w / q) = (q / w) * y := by field_simp [hq.ne', hw.ne']
      rw [ha]
      exact cuspFourierHeightPairing_scaled_integrand hy hw _ _
    _ = _ := spectralKLPhysical_dilation_real_integral (fun x => f x * g x) (div_pos hw hq)

end
end ArtinMatthews
