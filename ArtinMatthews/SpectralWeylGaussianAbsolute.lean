module

public import ArtinMatthews.SpectralWeylDimensionlessKernel
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute Gaussian bounds for the literal two-height orbital kernel.
The positive cosine-free radial kernel dominates it, so compact physical
tests admit genuine modulus/physical Fubini without oscillatory claims. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectralWeylRadialKernel_norm_le (A b X : ℝ) :
    ‖spectralWeylRadialKernel A b X‖ ≤ spectralWeylRadialKernel A 0 X := by
  unfold spectralWeylRadialKernel
  by_cases hX : Real.sqrt A < X
  · rw [ite_eq_left hX,ite_eq_left hX,zero_mul,Real.cos_zero,mul_one,norm_div,norm_mul]
    norm_num only [Real.norm_ofNat]
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (by norm_num : (0 : ℝ) ≤ 2) (Real.abs_cos_le_one _)) (Real.sqrt_nonneg _)
  · simp only [ite_eq_right hX,norm_zero,le_refl]

theorem spectralWeylDimensionlessKernel_joint_measurable (s t : ℝ) :
    Measurable (fun q : (ℝ × ℝ) × ℝ => spectralWeylDimensionlessKernel s t q.2 q.1.1 q.1.2) := by
  unfold spectralWeylDimensionlessKernel spectralWeylRadialKernel
  apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_snd) <;> fun_prop

theorem spectralWeylDimensionlessKernel_gaussian_abs_bound {x z p : ℝ}
    (hx : 0 < x) (hz : 0 < z) (hp : 0 < p) (s t : ℝ) :
    (∫ X in Ioi (0 : ℝ), ‖Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z‖) ≤
      Real.sqrt (Real.pi/p) := by
  have hA : 0 < 4*x*z := by positivity
  let b : ℝ := (s*x+t*z)/(2*Real.sqrt (x*z))
  have hle : (∫ X in Ioi (0 : ℝ), ‖Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z‖) ≤
      ∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylRadialKernel (4*x*z) 0 X := by
    apply integral_mono_ae (spectralWeylDimensionlessKernel_gaussian_integrable hx hz hp s t).norm.restrict
      (spectralWeylRadialGaussian_integrable hA hp 0).restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    rw [norm_mul,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_eq_abs,abs_of_pos hX]
    exact mul_le_mul_of_nonneg_left (spectralWeylRadialKernel_norm_le (4*x*z) b X)
      (mul_nonneg (Real.exp_pos _).le (le_of_lt hX))
  calc
    _ ≤ _ := hle
    _ = Real.sqrt (Real.pi/p)*Real.exp (-p*(4*x*z)) := by
      simpa only [spectralWeylRadialGaussian,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_div,sub_zero] using!
        spectralWeylRadialGaussian_integral hA hp 0
    _ ≤ _ := mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith))

theorem spectralWeyl_gaussian_complex_real (p X H : ℝ) :
    Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*(H : ℂ) =
      ((Real.exp (-p*X^2)*X*H : ℝ) : ℂ) := by
  rw [show -(p : ℂ)*(X : ℂ)^2 = ((-p*X^2 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_exp,← Complex.ofReal_mul,← Complex.ofReal_mul]

end ArtinMatthews
