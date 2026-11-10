module

public import ArtinMatthews.SpectralEisensteinHorizontalKernel
public import ArtinMatthews.SpectralCuspBesselTransform
public import ArtinMatthews.SpectralQuadraticFourierReduction
public import ArtinMatthews.SpectralQuadraticFourierBessel
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

/-! Height scaling of the actual phased Eisenstein row kernel and its
closed K-Bessel value, with frequency and height factors retained. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectralRealFourierPhase_scale (b y x : ℝ) :
    spectralRealFourierPhase b (y*x) = spectralRealFourierPhase (b*y) x := by
  unfold spectralRealFourierPhase
  congr 1
  push_cast
  ring

def eisensteinHorizontalFourier (s : ℂ) (b y : ℝ) : ℂ :=
  ∫ x : ℝ, eisensteinHorizontalKernel s y x*spectralRealFourierPhase b x

theorem eisensteinHorizontalFourier_integrable (s : ℂ) (hs : 1/2 < s.re)
    (b y : ℝ) (hy : 0 < y) :
    Integrable (fun x : ℝ => eisensteinHorizontalKernel s y x*spectralRealFourierPhase b x) := by
  apply (eisensteinHorizontalKernel_integrable s hs y hy).norm.mono'
  · unfold eisensteinHorizontalKernel spectralRealFourierPhase
    fun_prop
  · exact ae_of_all _ fun x => by rw [norm_mul,spectralRealFourierPhase_norm,mul_one]

theorem eisensteinHorizontalFourier_scale (s : ℂ) (b y : ℝ) (hy : 0 < y) :
    eisensteinHorizontalFourier s b y =
      (y : ℂ)^(1-s)*spectralQuadraticFourier s (b*y) := by
  let F (u : ℝ) := spectralQuadraticPower s u*spectralRealFourierPhase (b*y) u
  have he (x : ℝ) : eisensteinHorizontalKernel s y x*spectralRealFourierPhase b x =
      (y : ℂ)^(-s)*F (x/y) := by
    rw [eisensteinHorizontalKernel_eq s y hy]
    dsimp only [F]
    rw [← spectralRealFourierPhase_scale,mul_div_cancel₀ x hy.ne']
    ring
  unfold eisensteinHorizontalFourier
  simp_rw [he]
  rw [integral_const_mul,Measure.integral_comp_div,abs_of_pos hy,Complex.real_smul]
  have hpow : (y : ℂ)^(-s)*(y : ℂ) = (y : ℂ)^(1-s) := by
    calc
      _ = (y : ℂ)^(-s)*(y : ℂ)^(1 : ℂ) := by rw [Complex.cpow_one]
      _ = _ := by
        rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
        congr 1
        ring
  change (y : ℂ)^(-s)*((y : ℂ)*spectralQuadraticFourier s (b*y)) =
    (y : ℂ)^(1-s)*spectralQuadraticFourier s (b*y)
  rw [← mul_assoc,hpow]

theorem eisensteinHorizontalFourier_bessel (s : ℂ) (hs : 1/2 < s.re)
    (b y : ℝ) (hb : b ≠ 0) (hy : 0 < y) :
    eisensteinHorizontalFourier s b y =
      ((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s) *
        ((Real.pi*|b| : ℝ) : ℂ)^(s-1/2) *
          cuspBesselKernel (s-1/2) (2*Real.pi*|b|) y := by
  rw [eisensteinHorizontalFourier_scale s b y hy,
    spectralQuadraticFourier_bessel s hs (b*y) (mul_ne_zero hb hy.ne'),
    abs_mul,abs_of_pos hy,
    show Real.pi*(|b| * y)=(Real.pi*|b|)*y by ring,
    Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity : 0 ≤ Real.pi*|b|) hy.le,
    show 2*Real.pi*(|b| * y)=(2*Real.pi*|b|)*y by ring]
  have hpow : (y : ℂ)^(1-s)*(y : ℂ)^(s-1/2) = (Real.sqrt y : ℂ) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne'),
      show (1-s)+(s-1/2)=(1/2 : ℂ) by ring,Real.sqrt_eq_rpow,Complex.ofReal_cpow hy.le]
    norm_num
  unfold cuspBesselKernel
  calc
    _ = (((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s) *
        ((Real.pi*|b| : ℝ) : ℂ)^(s-1/2)) *
        ((y : ℂ)^(1-s)*(y : ℂ)^(s-1/2)) *
          OAI.CubicEisenstein.schlafliBesselK (s-1/2) ((2*Real.pi*|b|)*y) := by ring
    _ = _ := by rw [hpow];ring

end ArtinMatthews

