module

public import ArtinMatthews.SourceFiniteFiberScattering
public import ArtinMatthews.SourceKPCuspHeightConstantTerm
public import ArtinMatthews.SourceKPCuspNativeTraceSlice
public import ArtinMatthews.SourceKPCuspRepresentativeFourier
public import ArtinMatthews.SourceKPCuspResidualFourierValue
public import ArtinMatthews.SourceKPCuspFourierMomentParameter
public import ArtinMatthews.SourceKPCuspRepresentativeFourierAE
public import ArtinMatthews.SourceKPCuspResidualDualProfile
public import ArtinMatthews.SourceKPCuspZeroResidueCoefficient
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

/-! The original residue Fourier profiles at all positive product heights
for a continuous native representative. Both constants are the already
defined actual finite coefficients. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourceHyperbolicGreen
open scoped NumberField nonZeroDivisors
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0) (qf : SourceKPFiniteAdeleProjective K hζ)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V
local notation "P" => sourceKPCuspPositiveHeights K
local notation "D[" d "]" => FractionalIdeal.dual ℤ ℚ
  ((Ideal.span ({d} : Set (𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)

theorem sourceKPCuspRepresentativeFourierCell_eq_value_of_dual
    (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf) (m : Kˣ) (hmd : (m : K) ∈ D[d])
    {T : ℝ} (hT : 1 ≤ T) (U : X → ℂ) (hU : ContinuousOn U (productUpper V))
    (hUae : U =ᵐ[productVolume V] sourceKPCompactChartPullback K hζ
      (sourceKPAutomorphicExceptionalResidue K hζ hT).val (QuotientGroup.mk qf))
    (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPCuspRepresentativeFourierCell K hζ d hd U (m : K) y =
      sourceKPCuspResidualFourierValue K hζ m hT qf *
        sourceKPTraceJacquetArchProfile K hζ m (1/6) y := by
  refine sourceKPCuspPositiveHeights_eq_of_compact_ae K
    (sourceKPCuspRepresentativeFourierCell K hζ d hd U (m : K))
    (fun z => sourceKPCuspResidualFourierValue K hζ m hT qf *
      sourceKPTraceJacquetArchProfile K hζ m (1/6) z) ?_ ?_ ?_ y hy
  · exact sourceKPCuspRepresentativeFourierCell_continuousOn K hζ d hd U hU (m : K)
  · exact continuousOn_const.mul
      (sourceKPCuspArchFourierProfile_continuousOn K hζ m
        (s := (1/6 : ℂ)) (by norm_num) P (fun _ hz => hz))
  · intro B hB hpos
    exact (sourceKPCuspRepresentativeFourierCell_ae_eq_residual K hζ d hd qf (m : K) hT
      U hUae B hB.measurableSet hpos).trans
      (sourceKPCuspResidualFourierCell_ae_eq_value_of_dual K hζ d hd qf hperiod m hmd
        B hB hpos hT)

theorem sourceKPCuspRepresentativeFourierCell_eq_zero_profile
    (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hM : ∀ s : ℂ, ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1 →
      sourceKPAdelicTraceIntertwiner K hζ s (1,qf) =
        sourceKPFiniteFiberScatteringContinuation K hζ qf S s)
    {T : ℝ} (hT : 1 ≤ T) (U : X → ℂ) (hU : ContinuousOn U (productUpper V))
    (hUae : U =ᵐ[productVolume V] sourceKPCompactChartPullback K hζ
      (sourceKPAutomorphicExceptionalResidue K hζ hT).val (QuotientGroup.mk qf))
    (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPCuspRepresentativeFourierCell K hζ d hd U (0 : K) y =
      sourceKPFiniteFiberScatteringResidue K hζ qf S *
        ((sourceKPCuspArchHeight K y ^ (1/3 : ℝ) : ℝ) : ℂ) := by
  refine sourceKPCuspPositiveHeights_eq_of_compact_ae K
    (sourceKPCuspRepresentativeFourierCell K hζ d hd U (0 : K))
    (fun z => sourceKPFiniteFiberScatteringResidue K hζ qf S *
      ((sourceKPCuspArchHeight K z ^ (1/3 : ℝ) : ℝ) : ℂ)) ?_ ?_ ?_ y hy
  · exact sourceKPCuspRepresentativeFourierCell_continuousOn K hζ d hd U hU 0
  · exact (continuous_const.mul (Complex.continuous_ofReal.comp
      ((Real.continuous_rpow_const (q := (1/3 : ℝ)) (by norm_num)).comp
        (sourceKPCuspArchHeight_continuous K)))).continuousOn
  · intro B hB hpos
    exact (sourceKPCuspRepresentativeFourierCell_ae_eq_residual K hζ d hd qf 0 hT
      U hUae B hB.measurableSet hpos).trans
      (sourceKPCuspResidualZeroCell_ae_eq K hζ d hd qf hperiod S hM hT B hB hpos)

end
end ArtinMatthews
