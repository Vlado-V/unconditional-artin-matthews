module

public import ArtinMatthews.VaryingKummerAnalyticMixedMellinLeftIntegral
public import ArtinMatthews.VaryingKummerAnalyticDedekindPrimePowerMellinTerms
public import ArtinMatthews.VaryingKummerAnalyticDedekindPrimePowerMellinCanonical
public import ArtinMatthews.VaryingKummerAnalyticMixedMellinRectangle
public import ArtinMatthews.VaryingKummerAnalyticMixedMellinZeroLimit
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
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Passing the exact genuine Dedekind residue rectangle to infinite height.
The only remaining geometric inputs are a zero-avoiding height sequence and
vanishing horizontal edges; vertical convergence and the actual zero-sum
limit are discharged from their proved analytic theorems. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set Filter OAI.Ostmann
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped Classical Topology BigOperators Interval ContDiff
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
  (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f)
  {x : ℝ} (hx : 0<x) (T : ℕ → ℝ) (hpos : ∀ n,0<T n)
  (hlim : Tendsto T atTop atTop)
  (havoid : ∀ n ρ,mixedCompletedDedekindXi K ρ=0 → |ρ.im| ≠ T n)
  (htop : Tendsto (fun n => ∫ u in (-(1/2 : ℝ))..2,
    mixedExplicitFormulaIntegrand K f x ((u : ℂ)+(T n : ℂ)*I)) atTop (𝓝 0))
  (hbot : Tendsto (fun n => ∫ u in (-(1/2 : ℝ))..2,
    mixedExplicitFormulaIntegrand K f x ((u : ℂ)+((-T n : ℝ) : ℂ)*I)) atTop (𝓝 0))
include hcompact hpositive hsmooth hx hpos hlim havoid htop hbot

theorem mixedMellin_contour_limit_of_horizontal_limits :
    I*(∫ t : ℝ,mixedExplicitFormulaIntegrand K f x (2+(t : ℂ)*I))-
      I*(∫ t : ℝ,mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t)) =
      (2*(Real.pi : ℂ)*I)*((x : ℂ)*mellin f 1 -
        ∑' ρ,(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ*(x : ℂ)^ρ -
        (((InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)*mellin f 0) := by
  have htneg : Tendsto (fun n => -T n) atTop atBot := tendsto_neg_atTop_atBot.comp hlim
  have hri := dedekindPrimePower_canonical_mellin_integrable K f hcompact hpositive hsmooth hx
    (σ := 2) (by norm_num)
  obtain ⟨A,hA,hleft⟩ := exists_mixedMellin_left_integral_bound f hcompact hpositive hsmooth
  have hli := (hleft K x hx).1
  have hr := intervalIntegral_tendsto_integral hri htneg hlim
  have hl := intervalIntegral_tendsto_integral hli htneg hlim
  have hbd : Tendsto (fun n => rectangleBoundaryIntegral (mixedExplicitFormulaIntegrand K f x)
      (-(1/2)) 2 (-T n) (T n)) atTop
      (𝓝 (I*(∫ t : ℝ,mixedExplicitFormulaIntegrand K f x (2+(t : ℂ)*I))-
        I*(∫ t : ℝ,mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t)))) := by
    simpa only [rectangleBoundaryIntegral,mixedMellinLeftLine,Complex.ofReal_ofNat,
      Complex.ofReal_neg,zero_sub,zero_add,sub_zero,neg_mul] using
      ((hbot.sub htop).add (hr.const_mul I)).sub (hl.const_mul I)
  have hs := mixedMellin_zero_sum_tendsto K f hcompact hpositive hsmooth hx hlim
  have hres : Tendsto (fun n => (2*(Real.pi : ℂ)*I)*((x : ℂ)*mellin f 1 -
      ∑ ρ ∈ mixedContourZeros K (T n),
        (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ*(x : ℂ)^ρ -
      (((InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)*mellin f 0))
      atTop (𝓝 ((2*(Real.pi : ℂ)*I)*((x : ℂ)*mellin f 1 -
        ∑' ρ,(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ*(x : ℂ)^ρ -
        (((InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)*mellin f 0))) :=
    tendsto_const_nhds.mul ((tendsto_const_nhds.sub hs).sub_const _)
  apply tendsto_nhds_unique hbd
  apply hres.congr
  intro n
  exact (mixedMellin_rectangle_identity K f hcompact hpositive hsmooth.continuous hx
    (hpos n) (havoid n)).symm

theorem dedekindPrimePower_explicitFormula_of_horizontal_limits :
    (∑' i : DedekindPrimePowerIndex K,
      (Real.log (Ideal.absNorm i.2.1.val) : ℂ)*f ((dedekindPrimePowerNorm K i : ℝ)/x)) =
      (x : ℂ)*mellin f 1 -
        ∑' ρ,(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ*(x : ℂ)^ρ -
        (((InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)*mellin f 0 +
        ((1/(2*Real.pi) : ℝ) : ℂ)*
          ∫ t : ℝ,mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t) := by
  have H := mixedMellin_contour_limit_of_horizontal_limits K f hcompact hpositive hsmooth hx
    T hpos hlim havoid htop hbot
  rw [dedekindPrimePower_smoothed_canonical_mellin K f hcompact hpositive hsmooth hx
    (σ := 2) (by norm_num)]
  have H' : (∫ t : ℝ,mixedExplicitFormulaIntegrand K f x (2+(t : ℂ)*I))-
      (∫ t : ℝ,mixedExplicitFormulaIntegrand K f x (mixedMellinLeftLine t)) =
      (2*(Real.pi : ℂ))*((x : ℂ)*mellin f 1 -
        ∑' ρ,(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ*(x : ℂ)^ρ -
        (((InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)*mellin f 0) := by
    apply mul_left_cancel₀ I_ne_zero
    linear_combination H
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat]
  rw [sub_eq_iff_eq_add.mp H']
  field_simp

end
end ArtinMatthews.VaryingKummerAnalytic
