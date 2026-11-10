module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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

/-! The actual Gaussian cosine integral, with its absolute convergence
and literal half-line normalization. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectralGaussianCosine_integrable {p : ℝ} (hp : 0 < p) (b : ℝ) :
    Integrable (fun u : ℝ => Real.exp (-p*u^2)*Real.cos (b*u)) := by
  apply (integrable_exp_neg_mul_sq hp).mono' (by fun_prop)
  filter_upwards with u
  rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

theorem spectralGaussianCosine_full {p : ℝ} (hp : 0 < p) (b : ℝ) :
    (∫ u : ℝ, Real.exp (-p*u^2)*Real.cos (b*u)) =
      Real.sqrt (Real.pi/p)*Real.exp (-(b^2)/(4*p)) := by
  let F : ℝ → ℂ := fun u => Complex.exp (-(p : ℂ)*(u : ℂ)^2+((b : ℂ)*Complex.I)*(u : ℂ)+0)
  have hi : Integrable F := integrable_cexp_quadratic (b := (p : ℂ)) hp _ _
  have h := integral_cexp_quadratic (b := -(p : ℂ)) (by simpa using neg_neg_of_pos hp)
    ((b : ℂ)*Complex.I) 0
  have hs : ((Real.pi : ℂ)/(p : ℂ))^(1/2 : ℂ) = (Real.sqrt (Real.pi/p) : ℂ) := by
    rw [← Complex.ofReal_div,
      show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (div_pos Real.pi_pos hp).le,← Real.sqrt_eq_rpow]
  have hR : (∫ u : ℝ, F u).re = Real.sqrt (Real.pi/p)*Real.exp (-(b^2)/(4*p)) := by
    change (∫ u : ℝ, Complex.exp (-(p : ℂ)*(u : ℂ)^2+((b : ℂ)*Complex.I)*(u : ℂ)+0)).re = _
    rw [h]
    rw [neg_neg,hs]
    have he : (0 : ℂ)-((b : ℂ)*Complex.I)^2/(4* -(p : ℂ)) = ((-(b^2)/(4*p) : ℝ) : ℂ) := by
      push_cast
      rw [mul_pow,Complex.I_sq]
      ring
    rw [he,← Complex.ofReal_exp,← Complex.ofReal_mul,Complex.ofReal_re]
  change RCLike.re (∫ u : ℝ, F u) = _ at hR
  rw [← integral_re hi] at hR
  convert hR using 1
  apply integral_congr_ae
  filter_upwards with u
  have he : -(p : ℂ)*(u : ℂ)^2+((b : ℂ)*Complex.I)*(u : ℂ)+0 =
      ((-p*u^2 : ℝ) : ℂ)+((b*u : ℝ) : ℂ)*Complex.I := by push_cast; ring
  dsimp only [F]
  rw [he]
  change _ = (Complex.exp (((-p*u^2 : ℝ) : ℂ)+((b*u : ℝ) : ℂ)*Complex.I)).re
  rw [Complex.exp_re]
  norm_num [pow_two,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]

theorem spectralGaussianCosine_Ioi {p : ℝ} (hp : 0 < p) (b : ℝ) :
    (2 : ℝ)*(∫ u in Ioi (0 : ℝ), Real.exp (-p*u^2)*Real.cos (b*u)) =
      Real.sqrt (Real.pi/p)*Real.exp (-(b^2)/(4*p)) := by
  let f : ℝ → ℝ := fun u => Real.exp (-p*u^2)*Real.cos (b*u)
  have hi : Integrable f := spectralGaussianCosine_integrable hp b
  have hn : (∫ u in Iic (0 : ℝ), f u) = ∫ u in Ioi (0 : ℝ), f u := by
    calc
      _ = ∫ u in Ioi (0 : ℝ), f (-u) := by
        simpa only [neg_zero] using (integral_comp_neg_Ioi (0 : ℝ) f).symm
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u _
        simp only [f,neg_sq,mul_neg,Real.cos_neg]
  have h := spectralGaussianCosine_full hp b
  rw [← intervalIntegral.integral_Iic_add_Ioi hi.restrict hi.restrict,hn] at h
  simpa only [two_mul] using h

end ArtinMatthews
