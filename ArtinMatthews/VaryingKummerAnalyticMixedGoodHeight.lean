module

public import ArtinMatthews.KummerSplittingDiscriminantBasis
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import ArtinMatthews.VaryingKummerAnalyticZeroHeightWindow
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticMixedXiBoundary
public import ArtinMatthews.VaryingKummerAnalyticMixedXiZeroStrip
public import ArtinMatthews.VaryingKummerAnalyticMixedZeroHeightUniform
public import ArtinMatthews.VaryingKummerAnalyticZeroHeightAvoidance
public import ArtinMatthews.VaryingKummerAnalyticZeroHeightCard
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

/-! Genuine zero-avoiding contour heights with field-uniform separation. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set
open OAI.PrimeDegreePackets.AnalyticGrowth
noncomputable section
universe u

theorem mixedCompletedDedekindXi_exists_avoiding_height
    (K : Type u) [Field K] [NumberField K] (T : ℝ) :
    ∃ t ∈ Icc T (T+1), ∀ ρ : ℂ, mixedCompletedDedekindXi K ρ = 0 →
      1/(2*(zeroHeightCount (mixedCompletedDedekindXi K) (T+1/2)+1)) ≤ |t-ρ.im| :=
  exists_zeroHeightCount_avoiding (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm)
    (fun ρ hρ => (mixedCompletedDedekindXi_zeros_in_strip K ρ hρ).2) T

theorem exists_mixedDedekind_good_height :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K], ∀ T : ℝ,
      ∃ t ∈ Icc T (T+1), ∀ ρ : ℂ, mixedCompletedDedekindXi K ρ = 0 →
        1/(2*(C*(Real.log |(discr K : ℝ)| +
          (Module.finrank ℚ K : ℝ)*Real.log (|T+1/2|+2))+1)) ≤ |t-ρ.im| := by
  obtain ⟨C,hC,hbound⟩ := exists_mixedDedekind_zeroHeight_bound.{u}
  refine ⟨C,hC,?_⟩
  intro K _ _ T
  obtain ⟨t,ht,havoid⟩ := mixedCompletedDedekindXi_exists_avoiding_height K T
  refine ⟨t,ht,?_⟩
  intro ρ hρ
  apply le_trans ?_ (havoid ρ hρ)
  apply one_div_le_one_div_of_le
  · have hc := zeroHeightWindow_card_le (mixedCompletedDedekindXi_entire K)
      (mixedCompletedDedekindXi_zero_ne_zero K)
      (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm)
      (fun ρ hρ => (mixedCompletedDedekindXi_zeros_in_strip K ρ hρ).2) (T+1/2)
    have hnonneg : 0 ≤ zeroHeightCount (mixedCompletedDedekindXi K) (T+1/2) :=
      (Nat.cast_nonneg _).trans hc
    positivity
  · have h := hbound K (T+1/2)
    linarith

theorem exists_primeKummer_good_height :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℤ), a ≠ 0 → a ≠ 1 → a ≠ -1 →
      ∀ (q : ℕ), q.Prime → a.natAbs ≤ q → ∀ T : ℝ,
        ∃ t ∈ Icc T (T+1), ∀ ρ : ℂ, mixedCompletedDedekindXi (primeKummerField q a) ρ = 0 →
          1/(2*(C*(q : ℝ)^2*Real.log ((q : ℝ)*(|T+1/2|+2))+1)) ≤ |t-ρ.im| := by
  obtain ⟨C,hC,hbound⟩ := exists_primeKummer_zeroHeight_bound
  refine ⟨C,hC,?_⟩
  intro a ha0 ha1 ham1 q hq haq T
  obtain ⟨t,ht,havoid⟩ := mixedCompletedDedekindXi_exists_avoiding_height (primeKummerField q a) T
  refine ⟨t,ht,?_⟩
  intro ρ hρ
  apply le_trans ?_ (havoid ρ hρ)
  apply one_div_le_one_div_of_le
  · have hc := zeroHeightWindow_card_le (mixedCompletedDedekindXi_entire (primeKummerField q a))
      (mixedCompletedDedekindXi_zero_ne_zero (primeKummerField q a))
      (fun z => (mixedCompletedDedekindXi_functional_equation (primeKummerField q a) z).symm)
      (fun ρ hρ => (mixedCompletedDedekindXi_zeros_in_strip (primeKummerField q a) ρ hρ).2) (T+1/2)
    have hnonneg : 0 ≤ zeroHeightCount (mixedCompletedDedekindXi (primeKummerField q a)) (T+1/2) :=
      (Nat.cast_nonneg _).trans hc
    positivity
  · have h := hbound a ha0 ha1 ham1 q hq haq (T+1/2)
    linarith

end
end ArtinMatthews.VaryingKummerAnalytic
