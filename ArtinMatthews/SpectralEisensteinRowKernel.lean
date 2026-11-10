module

public import ArtinMatthews.SpectralEisensteinHorizontalKernel
public import ArtinMatthews.SpectralIntegerPeriodUnfolding
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Exact positive-row scaling and the absolutely justified period-one orbital integral. -/
noncomputable section
open Set MeasureTheory
namespace ArtinMatthews

def eisensteinRealRowTerm (s : ℂ) (c d x y : ℝ) : ℂ :=
  ((y/((c*x+d)^2+(c*y)^2):ℝ):ℂ)^s

theorem eisensteinRealRowTerm_factor (s : ℂ) (c : ℝ) (hc : 0<c)
    (d x y : ℝ) (hy : 0<y) :
    eisensteinRealRowTerm s c d x y =
      (c:ℂ)^(-2*s)*eisensteinHorizontalKernel s y (x+d/c) := by
  have hQ : (c*x+d)^2+(c*y)^2=c^2*((x+d/c)^2+y^2) := by
    field_simp [hc.ne']
  have hB : 0<(x+d/c)^2+y^2 := by positivity
  have he : y/(c^2*((x+d/c)^2+y^2)) = (c^2)⁻¹*(y/((x+d/c)^2+y^2)) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hp : (((c^2:ℝ):ℂ)^s)=(c:ℂ)^(2*s) := by
    simpa [Real.rpow_two] using (Complex.cpow_mul_ofReal_nonneg hc.le 2 s).symm
  unfold eisensteinRealRowTerm eisensteinHorizontalKernel
  rw [hQ,he,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity)
    (div_nonneg hy.le hB.le),Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg
    (sq_nonneg c),hp,← Complex.cpow_neg]
  rw [show -(2*s)= -2*s by ring]

theorem eisensteinRealRowTerm_translate (s : ℂ) (c : ℝ) (hc : 0<c)
    (a x y : ℝ) (hy : 0<y) (k : ℤ) :
    eisensteinRealRowTerm s c (a+c*(k:ℝ)) x y =
      (c:ℂ)^(-2*s)*eisensteinHorizontalKernel s y (x+(k:ℝ)+a/c) := by
  rw [eisensteinRealRowTerm_factor s c hc _ _ _ hy]
  congr 2
  field_simp [hc.ne']
  ring

theorem eisensteinRealRowTerm_translate_integral (s : ℂ) (hs : 1/2<s.re)
    (c : ℝ) (hc : 0<c) (a y : ℝ) (hy : 0<y) :
    (∑' k : ℤ, ∫ x in (0:ℝ)..1, eisensteinRealRowTerm s c (a+c*(k:ℝ)) x y) =
      (c:ℂ)^(-2*s)*(y:ℂ)^(1-s)*
        ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s) := by
  simp_rw [eisensteinRealRowTerm_translate s c hc a _ y hy,
    intervalIntegral.integral_const_mul]
  rw [tsum_mul_left,spectralIntegerPeriodUnfolding_shift _
    (eisensteinHorizontalKernel_integrable s hs y hy) (a/c),
    eisensteinHorizontalKernel_integral s hs y hy]
  ring

end ArtinMatthews
