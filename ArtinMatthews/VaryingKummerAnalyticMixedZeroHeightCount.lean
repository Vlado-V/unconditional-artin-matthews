module

public import ArtinMatthews.VaryingKummerAnalyticZeroHeightWindow
public import ArtinMatthews.VaryingKummerAnalyticComplexZeroPole
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import ArtinMatthews.VaryingKummerAnalyticComplexZeroCount
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindGrowth
public import ArtinMatthews.VaryingKummerAnalyticMixedXiBoundary
public import ArtinMatthews.VaryingKummerAnalyticMixedXiZeroStrip
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

/-! Actual mixed-signature Dedekind zero-pole identity and height-window
multiplicity bounds, with no assumed zero-strip or growth property. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField Complex
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedCompletedDedekindXi_hasSum_complexZeroPole {s : ℂ} (hs : 1 < s.re) :
    HasSum (complexZeroPole (mixedCompletedDedekindXi K) s)
      (logDeriv (mixedCompletedDedekindXi K) s).re :=
  hasSum_complexZeroPole (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K)
    (mixedCompletedDedekindXi_hasSubquadraticGrowth K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm)
    (fun ρ hρ => (mixedCompletedDedekindXi_zeros_in_strip K ρ hρ).2) hs

theorem mixedCompletedDedekindXi_finite_height_window_bound
    (S : Finset ℂ) (T : ℝ) (hT : ∀ ρ ∈ S, |T-ρ.im| ≤ 1) :
    (∑ ρ ∈ S, (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℝ)) ≤
      5*(logDeriv (mixedCompletedDedekindXi K) (⟨2,T⟩ : ℂ)).re :=
  finite_zero_height_window_bound (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K)
    (mixedCompletedDedekindXi_hasSubquadraticGrowth K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm)
    (fun ρ hρ => (mixedCompletedDedekindXi_zeros_in_strip K ρ hρ).2) S T hT

theorem mixedCompletedDedekindXi_zeroHeightCount_le_logDeriv (T : ℝ) :
    zeroHeightCount (mixedCompletedDedekindXi K) T ≤
      5*(logDeriv (mixedCompletedDedekindXi K) (⟨2,T⟩ : ℂ)).re :=
  zeroHeightCount_le_logDeriv (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K)
    (mixedCompletedDedekindXi_hasSubquadraticGrowth K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm)
    (fun ρ hρ => (mixedCompletedDedekindXi_zeros_in_strip K ρ hρ).2) T

end
end ArtinMatthews.VaryingKummerAnalytic
