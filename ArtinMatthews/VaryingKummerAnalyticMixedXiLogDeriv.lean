module

public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import ArtinMatthews.VaryingKummerAnalyticDedekindNonvanishing
public import ArtinMatthews.VaryingKummerAnalyticMixedXiLogDerivBase
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The unconditional logarithmic derivative formula for the actual
mixed-signature completed Dedekind xi function. -/
noncomputable section
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

/-- Every factor is genuinely nonzero in Re(s)>1 by the actual Euler-product
and Gamma theorems; no nonvanishing hypothesis is required here. -/
theorem mixedCompletedDedekindXi_logDeriv {s : ℂ} (hs : 1 < s.re) :
    logDeriv (mixedCompletedDedekindXi K) s =
      1 / s + 1 / (s - 1) + (Real.log (mixedDiscriminantScale K) : ℂ) +
        logDeriv (mixedGammaFactor K) s + logDeriv (NumberField.dedekindZeta K) s :=
  mixedCompletedDedekindXi_logDeriv_of_zeta_ne_zero K hs
    (dedekindZeta_ne_zero_of_one_lt_re K hs)

/-- The corresponding exact real-part identity, suitable for the pole-sum
and Gamma estimates. -/
theorem mixedCompletedDedekindXi_logDeriv_re {s : ℂ} (hs : 1 < s.re) :
    (logDeriv (mixedCompletedDedekindXi K) s).re =
      (1 / s).re + (1 / (s - 1)).re + Real.log (mixedDiscriminantScale K) +
        (logDeriv (mixedGammaFactor K) s).re +
          (logDeriv (NumberField.dedekindZeta K) s).re := by
  rw [mixedCompletedDedekindXi_logDeriv K hs]
  simp only [Complex.add_re, Complex.ofReal_re]

end ArtinMatthews.VaryingKummerAnalytic
