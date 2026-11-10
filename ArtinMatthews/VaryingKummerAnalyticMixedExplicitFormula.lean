module

public import ArtinMatthews.VaryingKummerAnalyticDedekindPrimePowerMellinTerms
public import ArtinMatthews.VaryingKummerAnalyticMixedMellinLeftIntegral
public import ArtinMatthews.VaryingKummerAnalyticMixedHorizontalContour
public import ArtinMatthews.VaryingKummerAnalyticMixedMellinContourLimit
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The unconditional smoothed explicit formula for the genuine Dedekind zeta
function of an arbitrary number field.  Both the actual prime-ideal-power
series and the full multiplicity-weighted zero sum are absolutely convergent;
the contour heights and all boundary limits are constructed, not assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set Filter
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped Classical Topology BigOperators Interval ContDiff
noncomputable section

/-- Exact smooth prime-ideal explicit formula, with the genuine left integral
and the exact archimedean vanishing order at zero. -/
theorem dedekindPrimePower_explicitFormula
    (K : Type*) [Field K] [NumberField K] (f : ℝ → ℂ)
    (hcompact : HasCompactSupport f) (hpositive : tsupport f ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ f) {x : ℝ} (hx : 0 < x) :
    (∑' i : DedekindPrimePowerIndex K,
      (Real.log (Ideal.absNorm i.2.1.val) : ℂ)*f ((dedekindPrimePowerNorm K i : ℝ)/x)) =
      (x : ℂ)*mellin f 1 -
        ∑' ρ,(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ*(x : ℂ)^ρ -
        (((InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)*mellin f 0 +
        ((1/(2*Real.pi) : ℝ) : ℂ)*
          ∫ t : ℝ,mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t) := by
  obtain ⟨T,hT,hlim,havoid,htop,hbot⟩ :=
    exists_mixedMellin_horizontal_integrals_tendsto_zero K f hcompact hpositive hsmooth hx
  have hmk (a b : ℝ) : (⟨a,b⟩ : ℂ) = (a : ℂ)+(b : ℂ)*I := by
    apply Complex.ext <;> simp
  apply dedekindPrimePower_explicitFormula_of_horizontal_limits K f hcompact hpositive hsmooth
    hx T (fun n => by linarith [(hT n).1]) hlim havoid
  · simpa only [hmk] using htop
  · simpa only [hmk] using hbot

end
end ArtinMatthews.VaryingKummerAnalytic
