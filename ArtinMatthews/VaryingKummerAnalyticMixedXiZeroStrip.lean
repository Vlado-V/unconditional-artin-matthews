module

public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import ArtinMatthews.VaryingKummerAnalyticZeroReflection
public import ArtinMatthews.VaryingKummerAnalyticDedekindNonvanishing
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindGrowth
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAnalytic
public import ArtinMatthews.VaryingKummerAnalyticMixedXiBoundary
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

/-! The actual mixed-signature completed Dedekind xi has all its zeros in the
closed critical strip. Consequently its actual zero-pole sum is its logarithmic
derivative on the real half-line to the right of one. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open ArtinMatthews.ReusedGrowth OAI.PrimeDegreePackets.AnalyticGrowth
open scoped Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedCompletedDedekindXi_nonzero_right {s : ℂ} (hs : 1 < s.re) :
    mixedCompletedDedekindXi K s ≠ 0 := by
  rw [mixedCompletedDedekindXi_eq K hs]
  have hs1 : s-1 ≠ 0 := sub_ne_zero.mpr (by
    intro h
    simp only [h, Complex.one_re, lt_self_iff_false] at hs)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (Complex.ne_zero_of_one_lt_re hs) hs1)
    (Complex.cpow_ne_zero_iff.mpr (Or.inl
      (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'))))
    (mixedGammaFactor_ne_zero K (lt_trans zero_lt_one hs)))
    (dedekindZeta_ne_zero_of_one_lt_re K hs)

theorem mixedCompletedDedekindXi_nonzero_left {s : ℂ} (hs : s.re < 0) :
    mixedCompletedDedekindXi K s ≠ 0 := by
  rw [mixedCompletedDedekindXi_functional_equation]
  apply mixedCompletedDedekindXi_nonzero_right K
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- Actual zeros, with no assumed critical-strip schema. -/
theorem mixedCompletedDedekindXi_zeros_in_strip (ρ : ℂ)
    (hρ : mixedCompletedDedekindXi K ρ = 0) : 0 ≤ ρ.re ∧ ρ.re ≤ 1 := by
  constructor
  · by_contra h
    exact mixedCompletedDedekindXi_nonzero_left K (lt_of_not_ge h) hρ
  · by_contra h
    exact mixedCompletedDedekindXi_nonzero_right K (lt_of_not_ge h) hρ

/-- Exact summation over the zeros of the genuine completed Dedekind function. -/
theorem mixedCompletedDedekindXi_hasSum_realZeroPole {σ : ℝ} (hσ : 1 < σ) :
    HasSum (realZeroPole (mixedCompletedDedekindXi K) σ)
      (logDeriv (mixedCompletedDedekindXi K) (σ : ℂ)).re := by
  exact hasSum_realZeroPole (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K)
    (mixedCompletedDedekindXi_hasSubquadraticGrowth K)
    (fun z => (mixedCompletedDedekindXi_functional_equation K z).symm)
    (fun ρ hρ => (mixedCompletedDedekindXi_zeros_in_strip K ρ hρ).2) hσ

theorem mixedCompletedDedekindXi_realZeroPole_nonneg {σ : ℝ} (hσ : 1 < σ) (ρ : ℂ) :
    0 ≤ realZeroPole (mixedCompletedDedekindXi K) σ ρ :=
  realZeroPole_nonneg (mixedCompletedDedekindXi_entire K)
    (mixedCompletedDedekindXi_zero_ne_zero K)
    (fun ρ hρ => (mixedCompletedDedekindXi_zeros_in_strip K ρ hρ).2) hσ ρ

end
end ArtinMatthews.VaryingKummerAnalytic
