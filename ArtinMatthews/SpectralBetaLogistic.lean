module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine beta integral in logarithmic odds coordinates. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

def spectralBetaLogProfile (a b : ℂ) (u : ℝ) : ℂ :=
  (Real.sigmoid u : ℂ)^a * ((1-Real.sigmoid u : ℝ) : ℂ)^b

theorem spectralBetaLogProfile_continuous (a b : ℂ) : Continuous (spectralBetaLogProfile a b) := by
  unfold spectralBetaLogProfile
  apply Continuous.mul
  · apply Continuous.cpow (by fun_prop) continuous_const
    intro u
    exact Complex.ofReal_mem_slitPlane.mpr (Real.sigmoid_pos u)
  · apply Continuous.cpow (by fun_prop) continuous_const
    intro u
    exact Complex.ofReal_mem_slitPlane.mpr (sub_pos.mpr (Real.sigmoid_lt_one u))

theorem sigmoid_log_odds (u : ℝ) :
    Real.log (Real.sigmoid u)-Real.log (1-Real.sigmoid u) = u := by
  have hs : 0 < Real.sigmoid u := Real.sigmoid_pos u
  have ht : 0 < 1-Real.sigmoid u := sub_pos.mpr (Real.sigmoid_lt_one u)
  have he : Real.sigmoid u/(1-Real.sigmoid u) = Real.exp u := by
    rw [← Real.sigmoid_neg,Real.sigmoid_def,Real.sigmoid_def,Real.exp_neg]
    field_simp [(Real.exp_pos u).ne']
    ring
  rw [← Real.log_div hs.ne' ht.ne',he,Real.log_exp]

theorem spectralBetaLogProfile_jacobian (a b : ℂ) (u : ℝ) :
    (Real.sigmoid u*(1-Real.sigmoid u)) •
      ((Real.sigmoid u : ℂ)^(a-1)*(1-(Real.sigmoid u : ℂ))^(b-1)) =
        spectralBetaLogProfile a b u := by
  have hs : (Real.sigmoid u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sigmoid_pos u).ne'
  have ht : ((1-Real.sigmoid u : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_pos.mpr (Real.sigmoid_lt_one u)).ne'
  have hp (z v : ℂ) (hz : z ≠ 0) : z*z^(v-1) = z^v := by
    calc
      _ = z^(1 : ℂ)*z^(v-1) := by rw [Complex.cpow_one]
      _ = z^(1+(v-1)) := (Complex.cpow_add _ _ hz).symm
      _ = _ := by congr 1; ring
  rw [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one]
  unfold spectralBetaLogProfile
  rw [Complex.ofReal_sub,Complex.ofReal_one]
  calc
    _ = ((Real.sigmoid u : ℂ)*(Real.sigmoid u : ℂ)^(a-1)) *
        ((1-(Real.sigmoid u : ℂ))*(1-(Real.sigmoid u : ℂ))^(b-1)) := by ring
    _ = _ := by rw [hp _ _ hs,hp _ _ (by simpa using ht)]

theorem spectralBetaLogProfile_integrable (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    Integrable (spectralBetaLogProfile a b) := by
  have hI : IntegrableOn (fun x : ℝ => (x : ℂ)^(a-1)*(1-(x : ℂ))^(b-1)) (Ioo 0 1) := by
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (Complex.betaIntegral_convergent ha hb).def'
  rw [← Real.range_sigmoid,← image_univ] at hI
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun u _ => (Real.hasDerivAt_sigmoid u).hasDerivWithinAt)
    Real.sigmoid_injective.injOn _).mp hI
  have he : ∀ u : ℝ, |Real.sigmoid u*(1-Real.sigmoid u)| =
      Real.sigmoid u*(1-Real.sigmoid u) := fun u => abs_of_pos
        (mul_pos (Real.sigmoid_pos u) (sub_pos.mpr (Real.sigmoid_lt_one u)))
  simpa only [he,spectralBetaLogProfile_jacobian,integrableOn_univ] using h

theorem spectralBetaLogProfile_integral (a b : ℂ) :
    (∫ u : ℝ, spectralBetaLogProfile a b u) = Complex.betaIntegral a b := by
  unfold Complex.betaIntegral
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),integral_Ioc_eq_integral_Ioo,
    ← Real.range_sigmoid,← image_univ]
  rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun u _ => (Real.hasDerivAt_sigmoid u).hasDerivWithinAt) Real.sigmoid_injective.injOn]
  rw [Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [abs_of_pos (mul_pos (Real.sigmoid_pos u) (sub_pos.mpr (Real.sigmoid_lt_one u)))]
  exact (spectralBetaLogProfile_jacobian a b u).symm

theorem spectralBetaLogProfile_shift (a b z : ℂ) (u : ℝ) :
    spectralBetaLogProfile (a+z) (b-z) u =
      spectralBetaLogProfile a b u * Complex.exp (z*(u : ℂ)) := by
  have hs : (Real.sigmoid u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sigmoid_pos u).ne'
  have ht : ((1-Real.sigmoid u : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_pos.mpr (Real.sigmoid_lt_one u)).ne'
  have he : (Real.sigmoid u : ℂ)^z * ((1-Real.sigmoid u : ℝ) : ℂ)^(-z) =
      Complex.exp (z*(u : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hs,Complex.cpow_def_of_ne_zero ht,← Complex.exp_add,
      ← Complex.ofReal_log (Real.sigmoid_pos u).le,
      ← Complex.ofReal_log (sub_pos.mpr (Real.sigmoid_lt_one u)).le]
    congr 1
    have hh := congrArg (fun t : ℝ => (t : ℂ)) (sigmoid_log_odds u)
    push_cast at hh
    linear_combination z*hh
  unfold spectralBetaLogProfile
  rw [Complex.cpow_add _ _ hs,show b-z = b+(-z) by ring,Complex.cpow_add _ _ ht]
  calc
    _ = ((Real.sigmoid u : ℂ)^a*((1-Real.sigmoid u : ℝ) : ℂ)^b) *
        ((Real.sigmoid u : ℂ)^z*((1-Real.sigmoid u : ℝ) : ℂ)^(-z)) := by ring
    _ = _ := by rw [he]

theorem spectralBetaLogProfile_reflect_product (a b c d : ℂ) (u : ℝ) :
    spectralBetaLogProfile a b u * spectralBetaLogProfile c d (-u) =
      spectralBetaLogProfile (a+d) (b+c) u := by
  have hs : (Real.sigmoid u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sigmoid_pos u).ne'
  have ht : ((1-Real.sigmoid u : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_pos.mpr (Real.sigmoid_lt_one u)).ne'
  unfold spectralBetaLogProfile
  rw [Real.sigmoid_neg,sub_sub_cancel]
  rw [Complex.cpow_add _ _ hs,Complex.cpow_add _ _ ht]
  ring

end ArtinMatthews
