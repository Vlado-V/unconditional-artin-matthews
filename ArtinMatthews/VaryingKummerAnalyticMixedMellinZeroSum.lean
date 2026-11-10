module

public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import OAI.NumberTheory.PrimePackets.AnalyticLogarithms
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindGrowth
public import ArtinMatthews.VaryingKummerAnalyticMixedXiBoundary
public import ArtinMatthews.VaryingKummerAnalyticMixedXiZeroStrip
public import ArtinMatthews.VaryingKummerAnalyticSmoothMellin
public import ArtinMatthews.VaryingKummerAnalyticWeightedZeroSum
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

/-! Absolute convergence of the actual Mellin-weighted nontrivial-zero sum,
including every multiplicity and the actual complex power of x. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped ContDiff BigOperators
noncomputable section
universe u

theorem mixedCompletedDedekindXi_mellin_zero_sum
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K],
      Summable (fun ρ => (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ) ∧
      (∑' ρ, ‖(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ‖) ≤
        C*(logDeriv (mixedCompletedDedekindXi K) 2).re := by
  obtain ⟨C,hC,hΦ⟩ := smoothMellin_explicitFormula_decay f hcompact hpositive hsmooth 2
  refine ⟨4*C,by positivity,?_⟩
  intro K _ _
  exact weighted_zero_summable_and_bound (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K)
    (mixedCompletedDedekindXi_hasSubquadraticGrowth K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm) hC.le
    (mixedCompletedDedekindXi_zeros_in_strip K)
    (fun ρ hρ => hΦ ρ (by linarith [(mixedCompletedDedekindXi_zeros_in_strip K ρ hρ).1])
      (by linarith [(mixedCompletedDedekindXi_zeros_in_strip K ρ hρ).2]))

lemma norm_cpow_strip_le_max {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hρ0 : 0 ≤ ρ.re) (hρ1 : ρ.re ≤ 1) :
    ‖(x : ℂ)^ρ‖ ≤ max 1 x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  by_cases h : x ≤ 1
  · exact (Real.rpow_le_one hx.le h hρ0).trans (le_max_left _ _)
  · exact (Real.rpow_le_self_of_one_le (le_of_not_ge h) hρ1).trans (le_max_right _ _)

theorem mixedCompletedDedekindXi_mellin_power_zero_sum
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K], ∀ x : ℝ, 0 < x →
      Summable (fun ρ => (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*
        mellin f ρ*(x : ℂ)^ρ) ∧
      (∑' ρ, ‖(zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*
        mellin f ρ*(x : ℂ)^ρ‖) ≤ C*max 1 x*(logDeriv (mixedCompletedDedekindXi K) 2).re := by
  obtain ⟨C,hC,hΦ⟩ := smoothMellin_explicitFormula_decay f hcompact hpositive hsmooth 2
  refine ⟨4*C,by positivity,?_⟩
  intro K _ _ x hx
  have hm : 0 ≤ max (1 : ℝ) x := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have H := weighted_zero_summable_and_bound (Φ := fun ρ => mellin f ρ*(x : ℂ)^ρ)
    (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K)
    (mixedCompletedDedekindXi_hasSubquadraticGrowth K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm)
    (mul_nonneg hC.le hm) (mixedCompletedDedekindXi_zeros_in_strip K) (fun ρ hρ => ?_)
  · simpa only [mul_assoc] using H
  · have hstrip := mixedCompletedDedekindXi_zeros_in_strip K ρ hρ
    rw [norm_mul]
    calc
      _ ≤ (C/(1+|ρ.im|)^2)*max 1 x := mul_le_mul
        (hΦ ρ (by linarith [hstrip.1]) (by linarith [hstrip.2]))
        (norm_cpow_strip_le_max hx hstrip.1 hstrip.2) (norm_nonneg _) (by positivity)
      _ = _ := by ring

end
end ArtinMatthews.VaryingKummerAnalytic
