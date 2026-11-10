module

public import ArtinMatthews.VaryingKummerAnalyticMixedDualShift
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualLattice
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualNormIdeal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! Exact cancellation of the discriminant, ideal norm, and complex-place
Gaussian scale in the completed Dedekind functional equation. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedDiscriminantScale_log :
    Real.log (mixedDiscriminantScale K) =
      -(InfinitePlace.nrComplexPlaces K : ℝ)*Real.log 2 + Real.log |(discr K : ℝ)|/2 := by
  unfold mixedDiscriminantScale
  rw [Real.log_mul (pow_ne_zero _ (by norm_num))
      (Real.sqrt_ne_zero'.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))),
    Real.log_pow, Real.log_inv, Real.log_sqrt (abs_nonneg _)]
  ring

theorem mixedDualRadialScale_sq_log :
    Real.log ((mixedDualRadialScale K)^2) =
      4*(InfinitePlace.nrComplexPlaces K : ℝ)*Real.log 2 / (Module.finrank ℚ K : ℝ) := by
  rw [Real.log_pow, mixedDualRadialScale, Real.log_exp, mixedDualMeanLog_signature]
  ring

/-- Positive-real base complex powers have the ordinary real logarithm. -/
theorem positiveReal_cpow_eq_exp {a : ℝ} (ha : 0 < a) (s : ℂ) :
    (a : ℂ)^s = Complex.exp ((Real.log a : ℝ)*s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'),
    ← Complex.ofReal_log ha.le]

/-- Every constant in the actual ideal functional equation is accounted for. -/
theorem mixedFunctionalEquation_coefficient
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (mixedDiscriminantScale K : ℂ)^s *
      ((FractionalIdeal.absNorm I.1 : ℝ) : ℂ)^s *
      (((FractionalIdeal.absNorm I.1 : ℝ)*mixedDiscriminantScale K : ℝ) : ℂ)⁻¹ *
      (((mixedDualRadialScale K)^2 : ℝ) : ℂ)^(-((Module.finrank ℚ K : ℂ)*(1-s)/2)) =
    (mixedDiscriminantScale K : ℂ)^(1-s) *
      ((FractionalIdeal.absNorm (mixedTraceDualIdeal K I).1 : ℝ) : ℂ)^(1-s) := by
  have hA := fractionalIdeal_absNorm_pos I
  have hC := mixedDiscriminantScale_pos K
  have hD : 0 < |(discr K : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have he : (((FractionalIdeal.absNorm I.1 : ℝ)*mixedDiscriminantScale K : ℝ) : ℂ)⁻¹ =
      Complex.exp (-(Real.log ((FractionalIdeal.absNorm I.1 : ℝ)*mixedDiscriminantScale K) : ℝ)) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg,
      Real.exp_log (mul_pos hA hC), Complex.ofReal_inv]
  rw [he, positiveReal_cpow_eq_exp hC, positiveReal_cpow_eq_exp hA,
    positiveReal_cpow_eq_exp (sq_pos_of_pos (mixedDualRadialScale_pos K)),
    positiveReal_cpow_eq_exp hC,
    positiveReal_cpow_eq_exp (fractionalIdeal_absNorm_pos (mixedTraceDualIdeal K I))]
  rw [Real.log_mul hA.ne' hC.ne', mixedTraceDualIdeal_absNorm,
    Real.log_inv, Real.log_mul hD.ne' hA.ne',
    mixedDiscriminantScale_log, mixedDualRadialScale_sq_log]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  have hn : (Module.finrank ℚ K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  field_simp
  ring

end
end ArtinMatthews.VaryingKummerAnalytic
