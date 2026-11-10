module

public import ArtinMatthews.SpectralQuadraticBetaIntegral
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

/-! Exact height scaling and absolute integrability of the unfolded horizontal kernel. -/
noncomputable section
open Set MeasureTheory
namespace ArtinMatthews

def eisensteinHorizontalKernel (s : ℂ) (y u : ℝ) : ℂ := ((y/(u^2+y^2):ℝ):ℂ)^s

theorem eisensteinHorizontalKernel_eq (s : ℂ) (y : ℝ) (hy : 0<y) (u : ℝ) :
    eisensteinHorizontalKernel s y u = (y:ℂ)^(-s)*spectralQuadraticPower s (u/y) := by
  have hQ : 0<1+(u/y)^2 := by positivity
  have he : y/(u^2+y^2) = y⁻¹*(1+(u/y)^2)⁻¹ := by
    field_simp [hy.ne',hQ.ne']
    ring
  unfold eisensteinHorizontalKernel spectralQuadraticPower
  rw [he,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr hy.le)
    (inv_nonneg.mpr hQ.le),Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg hy.le,
    Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg hQ.le,
    Complex.cpow_neg,Complex.cpow_neg]
  push_cast
  rfl

theorem eisensteinHorizontalKernel_integrable (s : ℂ) (hs : 1/2<s.re) (y : ℝ) (hy : 0<y) :
    Integrable (eisensteinHorizontalKernel s y) := by
  have h := (spectralQuadraticPower_integrable s hs).comp_mul_right' (inv_ne_zero hy.ne')
  have he : eisensteinHorizontalKernel s y =
      fun u => (y:ℂ)^(-s)*spectralQuadraticPower s (u/y) := funext (eisensteinHorizontalKernel_eq s y hy)
  rw [he]
  simpa only [div_eq_mul_inv] using h.const_mul ((y:ℂ)^(-s))

theorem eisensteinHorizontalKernel_integral (s : ℂ) (hs : 1/2<s.re) (y : ℝ) (hy : 0<y) :
    (∫ u : ℝ, eisensteinHorizontalKernel s y u) =
      (y:ℂ)^(1-s)*((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s) := by
  simp_rw [eisensteinHorizontalKernel_eq s y hy]
  rw [integral_const_mul,Measure.integral_comp_div,abs_of_pos hy,Complex.real_smul,
    spectralQuadraticPower_integral s hs]
  have hc : (y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [show (1-s:ℂ)= -s+1 by ring,Complex.cpow_add _ _ hc,Complex.cpow_one]
  ring

end ArtinMatthews
