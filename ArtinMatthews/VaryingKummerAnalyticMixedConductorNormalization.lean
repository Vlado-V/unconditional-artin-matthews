module

public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import ArtinMatthews.VaryingKummerAnalyticMixedDualShift
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualLattice
public import ArtinMatthews.VaryingKummerAnalyticMixedFunctionalNormalization
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualNormIdeal
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

/-! Exact conductor-dependent scalar normalization for the mixed Hecke
functional equation. Both the signature powers of two and the square root
of the genuine conductor norm are retained. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def mixedConductorScale (M : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  mixedDiscriminantScale K * Real.sqrt (FractionalIdeal.absNorm M.val : ℝ)

theorem mixedConductorScale_pos (M : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < mixedConductorScale K M :=
  mul_pos (mixedDiscriminantScale_pos K) (Real.sqrt_pos.mpr (fractionalIdeal_absNorm_pos M))

theorem mixedConductorFunctionalEquation_coefficient
    (M I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (mixedConductorScale K M : ℂ)^s *
      ((FractionalIdeal.absNorm I.val : ℝ) : ℂ)^s *
      (((FractionalIdeal.absNorm (M*I).val : ℝ)*mixedDiscriminantScale K : ℝ) : ℂ)⁻¹ *
      (Real.sqrt (FractionalIdeal.absNorm M.val : ℝ):ℂ) *
      (((mixedDualRadialScale K)^2 : ℝ) : ℂ)^(-((Module.finrank ℚ K : ℂ)*(1-s)/2)) =
    (mixedConductorScale K M : ℂ)^(1-s) *
      ((FractionalIdeal.absNorm (mixedTraceDualIdeal K (M*I)).val : ℝ) : ℂ)^(1-s) := by
  have hA := fractionalIdeal_absNorm_pos I
  have hB := fractionalIdeal_absNorm_pos M
  have hAB := fractionalIdeal_absNorm_pos (M*I)
  have hC := mixedDiscriminantScale_pos K
  have hD : 0 < |(discr K : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hS := Real.sqrt_pos.mpr hB
  have he : (((FractionalIdeal.absNorm (M*I).val : ℝ)*mixedDiscriminantScale K : ℝ) : ℂ)⁻¹ =
      Complex.exp (-(Real.log ((FractionalIdeal.absNorm (M*I).val : ℝ)*mixedDiscriminantScale K) : ℝ)) := by
    rw [← Complex.ofReal_neg,← Complex.ofReal_exp,Real.exp_neg,
      Real.exp_log (mul_pos hAB hC),Complex.ofReal_inv]
  have hsqrt : (Real.sqrt (FractionalIdeal.absNorm M.val : ℝ):ℂ) =
      Complex.exp ((Real.log (Real.sqrt (FractionalIdeal.absNorm M.val : ℝ)):ℝ):ℂ) := by
    rw [← Complex.ofReal_exp,Real.exp_log hS]
  rw [he,hsqrt,positiveReal_cpow_eq_exp (mixedConductorScale_pos K M),
    positiveReal_cpow_eq_exp hA,
    positiveReal_cpow_eq_exp (sq_pos_of_pos (mixedDualRadialScale_pos K)),
    positiveReal_cpow_eq_exp (mixedConductorScale_pos K M),
    positiveReal_cpow_eq_exp (fractionalIdeal_absNorm_pos (mixedTraceDualIdeal K (M*I)))]
  rw [Real.log_mul hAB.ne' hC.ne',mixedTraceDualIdeal_absNorm,
    Real.log_inv,Real.log_mul hD.ne' hAB.ne']
  have hnMI : (FractionalIdeal.absNorm (M*I).val : ℝ) =
      (FractionalIdeal.absNorm M.val : ℝ)*(FractionalIdeal.absNorm I.val : ℝ) := by
    rw [Units.val_mul,map_mul,Rat.cast_mul]
  simp only [mixedConductorScale,Real.log_mul hC.ne' hS.ne',Real.log_sqrt hB.le,
    hnMI,Real.log_mul hB.ne' hA.ne',mixedDiscriminantScale_log,mixedDualRadialScale_sq_log]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  have hn : (Module.finrank ℚ K:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  field_simp
  ring

end
end ArtinMatthews.VaryingKummerAnalytic
