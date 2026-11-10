module

public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticUnitUnfolding
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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
import ArtinMatthews.VaryingKummerAnalyticGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine nonzero boundary values of the mixed-signature Dedekind completion.
They are obtained directly from the actual unit-domain volume and theta formula. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta ArtinMatthews.ReusedGrowth
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedUnitLogDomain_volume_pos : 0 < volume.real (mixedUnitLogDomain K) := by
  have : VAddInvariantMeasure (unitLattice K) (logSpace K) volume :=
    (inferInstance : VAddInvariantMeasure (unitLattice K).toAddSubgroup (logSpace K) volume)
  exact ENNReal.toReal_pos
    ((mixedUnitLogDomain_fundamental K).measure_ne_zero (NeZero.ne _))
    (mixedUnitLogDomain_bounded K).measure_lt_top.ne

theorem mixedIdealUnitXi_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    mixedIdealUnitXi K I 0 =
      ((volume.real (mixedUnitLogDomain K) * (Module.finrank ℚ K : ℝ)/2 : ℝ) : ℂ) := by
  unfold mixedIdealUnitXi
  simp only [mul_zero, zero_div, thetaMellinXi, zero_mul, zero_sub, sub_neg_eq_add,
    zero_add, mixedIdealIndex_card]
  rw [integral_const, measureReal_restrict_apply_univ]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_natCast, Complex.ofReal_ofNat]
  ring

theorem mixedCompletedDedekindXi_zero :
    mixedCompletedDedekindXi K 0 =
      (((mixedXiNormalization K)⁻¹ *
        (Fintype.card (ClassGroup (𝓞 K)) : ℝ) *
        (volume.real (mixedUnitLogDomain K) * (Module.finrank ℚ K : ℝ)/2) : ℝ) : ℂ) := by
  unfold mixedCompletedDedekindXi
  simp only [Complex.cpow_zero, mul_one, one_mul, mixedIdealUnitXi_zero,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  ring

theorem mixedCompletedDedekindXi_zero_pos : 0 < (mixedCompletedDedekindXi K 0).re := by
  rw [mixedCompletedDedekindXi_zero, Complex.ofReal_re]
  exact mul_pos (mul_pos (inv_pos.mpr (mixedXiNormalization_pos K))
    (Nat.cast_pos.mpr Fintype.card_pos))
    (div_pos (mul_pos (mixedUnitLogDomain_volume_pos K)
      (Nat.cast_pos.mpr Module.finrank_pos)) (by norm_num))

theorem mixedCompletedDedekindXi_zero_ne_zero : mixedCompletedDedekindXi K 0 ≠ 0 := by
  intro h
  have H := mixedCompletedDedekindXi_zero_pos K
  simp only [h, Complex.zero_re, lt_self_iff_false] at H

theorem mixedCompletedDedekindXi_one_ne_zero : mixedCompletedDedekindXi K 1 ≠ 0 := by
  rw [mixedCompletedDedekindXi_functional_equation, sub_self]
  exact mixedCompletedDedekindXi_zero_ne_zero K

end
end ArtinMatthews.VaryingKummerAnalytic
