module

public import ArtinMatthews.SpectralBesselCoshEvaluation
public import ArtinMatthews.SpectralKLTestLimit
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! A real cosine representation of the actual imaginary-order K kernel,
its joint measurability and a spectral-parameter-independent K_0 majorant. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology

namespace ArtinMatthews

def spectralKLRealKernel (t x : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.exp (-x*Real.cosh u)*Real.cos (t*u)

theorem spectralKCoshKernel_imaginary (t x u : ℝ) :
    spectralKCoshKernel ((t : ℂ)*Complex.I) x u =
      ((Real.exp (-x*Real.cosh u)*Real.cos (t*u) : ℝ) : ℂ) := by
  unfold spectralKCoshKernel
  rw [show (t : ℂ)*Complex.I*(u : ℂ) = ((t*u : ℝ) : ℂ)*Complex.I by push_cast; ring,
    Complex.cosh_mul_I]
  rw [← Complex.ofReal_cos]
  simp only [Complex.ofReal_mul,Complex.ofReal_exp]
  congr 2
  push_cast
  ring

theorem schlafliBesselK_imaginary_eq_realKernel (t : ℝ) {x : ℝ} (hx : 0 < x) :
    schlafliBesselK ((t : ℂ)*Complex.I) x = (spectralKLRealKernel t x : ℂ) := by
  rw [schlafliBesselK_cosh_integral _ hx]
  simp_rw [spectralKCoshKernel_imaginary]
  rw [integral_complex_ofReal]
  rfl

theorem spectralKLRealKernel_stronglyMeasurable :
    StronglyMeasurable (fun p : ℝ × ℝ => spectralKLRealKernel p.1 p.2) := by
  have hm : StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      Real.exp (-q.1.2*Real.cosh q.2)*Real.cos (q.1.1*q.2)) :=
    (by fun_prop : Continuous (fun q : (ℝ × ℝ) × ℝ =>
      Real.exp (-q.1.2*Real.cosh q.2)*Real.cos (q.1.1*q.2))).stronglyMeasurable
  exact hm.integral_prod_right' (ν := volume.restrict (Ioi 0))

theorem spectralKLRealKernel_integrand_integrable (t : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => Real.exp (-x*Real.cosh u)*Real.cos (t*u)) (Ioi 0) := by
  have hi := (spectralKCoshKernel_integrable ((t : ℂ)*Complex.I) hx).re
  apply hi.congr
  filter_upwards with u
  rw [spectralKCoshKernel_imaginary]
  rfl

theorem spectralKLRealKernel_zero_nonneg {x : ℝ} : 0 ≤ spectralKLRealKernel 0 x := by
  apply integral_nonneg
  intro u
  simp only [zero_mul,Real.cos_zero,mul_one]
  exact (Real.exp_pos _).le

theorem spectralKLRealKernel_norm_le_zero (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖spectralKLRealKernel t x‖ ≤ spectralKLRealKernel 0 x := by
  calc
    _ ≤ ∫ u in Ioi (0 : ℝ), ‖Real.exp (-x*Real.cosh u)*Real.cos (t*u)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi (0 : ℝ), Real.exp (-x*Real.cosh u)*Real.cos (0*u) := by
      apply integral_mono (spectralKLRealKernel_integrand_integrable t hx).norm
        (spectralKLRealKernel_integrand_integrable 0 hx)
      intro u
      dsimp only
      rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
      simp only [zero_mul,Real.cos_zero,mul_one,Real.norm_eq_abs]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
    _ = _ := rfl

theorem spectralKLRealKernel_zero_energy_integrable (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => x^(ε-1)*(spectralKLRealKernel 0 x)^2) (Ioi 0) := by
  have hi := (schlafliBesselK_product_imaginary_mellin_integrable 0 0 ε hε).norm
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,
    schlafliBesselK_imaginary_eq_realKernel 0 hx]
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.one_re,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg spectralKLRealKernel_zero_nonneg]
  ring

end ArtinMatthews
