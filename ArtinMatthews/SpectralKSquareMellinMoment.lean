module

public import ArtinMatthews.SpectralKLRealKernel
public import ArtinMatthews.SpectralBesselProductClosed
public import ArtinMatthews.SpectralBesselProductMellin
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

/-! Actual even moments of the real imaginary-order Schlaefli kernel,
from the checked closed K-product Mellin formula. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralKSquareMoment (k : ℕ) (t : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), x^(2*k)*(spectralKLRealKernel t x)^2

theorem spectralKSquareMoment_mellin_integrand (k : ℕ) (t x : ℝ) (hx : 0 < x) :
    (x : ℂ)^((2*(k : ℂ)+1)-1)*schlafliBesselK ((t : ℂ)*Complex.I) x*
      schlafliBesselK ((t : ℂ)*Complex.I) x =
      ((x^(2*k)*(spectralKLRealKernel t x)^2 : ℝ) : ℂ) := by
  rw [show (2*(k : ℂ)+1)-1 = ((2*k : ℕ) : ℂ) by push_cast; ring,
    Complex.cpow_natCast,schlafliBesselK_imaginary_eq_realKernel t hx]
  push_cast
  ring

theorem spectralKSquareMoment_integrable (k : ℕ) (t : ℝ) :
    IntegrableOn (fun x : ℝ => x^(2*k)*(spectralKLRealKernel t x)^2) (Ioi 0) := by
  let ν := (t : ℂ)*Complex.I
  let s := 2*(k : ℂ)+1
  have hs : |ν.re|+|ν.re| < s.re := by
    dsimp only [ν,s]
    norm_num [Complex.mul_re,Complex.add_re]
    positivity
  have hi := (schlafliBesselK_product_mellin_integrable_of_re_gt ν ν s hs).re
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  dsimp only [ν,s]
  rw [spectralKSquareMoment_mellin_integrand k t x hx]
  rfl

theorem spectralKSquareMoment_closed (k : ℕ) (t : ℝ) :
    let a := (k : ℂ)+1/2
    let s := 2*(k : ℂ)+1
    let ν := (t : ℂ)*Complex.I
    (spectralKSquareMoment k t : ℂ) =
      (2 : ℂ)^(s-3)*Complex.Gamma (a-ν)*Complex.Gamma a^2*Complex.Gamma (a+ν)/Complex.Gamma s := by
  dsimp only
  let ν := (t : ℂ)*Complex.I
  let s := 2*(k : ℂ)+1
  let a := (k : ℂ)+1/2
  have hs : |ν.re|+|ν.re| < s.re := by
    dsimp only [ν,s]
    norm_num [Complex.mul_re,Complex.add_re]
    positivity
  have hI : (spectralKSquareMoment k t : ℂ) =
      ∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*schlafliBesselK ν x*schlafliBesselK ν x := by
    unfold spectralKSquareMoment
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact (spectralKSquareMoment_mellin_integrand k t x hx).symm
  change _ = (2 : ℂ)^(s-3)*Complex.Gamma (a-ν)*Complex.Gamma a^2*Complex.Gamma (a+ν)/Complex.Gamma s
  rw [hI,schlafliBesselK_product_mellin_closed ν ν s hs,
    show (s-ν-ν)/2 = a-ν by dsimp only [s,a]; ring,
    show (s+ν-ν)/2 = a by dsimp only [s,a]; ring,
    show (s-ν+ν)/2 = a by dsimp only [s,a]; ring,
    show (s+ν+ν)/2 = a+ν by dsimp only [s,a]; ring,pow_two]
  ring

theorem spectral_Gamma_half_imaginary_product (t : ℝ) :
    Complex.Gamma ((1/2 : ℂ)-(t : ℂ)*Complex.I)*
      Complex.Gamma ((1/2 : ℂ)+(t : ℂ)*Complex.I) =
      (Real.pi : ℂ)/(Real.cosh (Real.pi*t) : ℂ) := by
  let ν := (t : ℂ)*Complex.I
  have hs : Complex.sin ((Real.pi : ℂ)*(1/2+ν)) = (Real.cosh (Real.pi*t) : ℂ) := by
    rw [show (Real.pi : ℂ)*(1/2+ν) = (Real.pi : ℂ)/2+((Real.pi*t : ℝ) : ℂ)*Complex.I by
      dsimp only [ν]
      push_cast
      ring,
      Complex.sin_add,Complex.sin_pi_div_two,Complex.cos_pi_div_two,one_mul,zero_mul,add_zero,
      Complex.cos_mul_I,Complex.ofReal_cosh]
  have h := Complex.Gamma_mul_Gamma_one_sub ((1/2 : ℂ)+ν)
  rw [hs,show (1 : ℂ)-(1/2+ν) = 1/2-ν by ring,mul_comm] at h
  exact h

theorem spectralKSquareMoment_zero (t : ℝ) :
    spectralKSquareMoment 0 t = Real.pi^2/(4*Real.cosh (Real.pi*t)) := by
  have hΓ : Complex.Gamma (1/2)^2 = (Real.pi : ℂ) := by
    have h := Complex.Gamma_mul_Gamma_one_sub (1/2 : ℂ)
    rw [show (1 : ℂ)-1/2 = 1/2 by ring,show (Real.pi : ℂ)*(1/2) = (Real.pi : ℂ)/2 by ring,
      Complex.sin_pi_div_two,div_one] at h
    simpa only [pow_two] using h
  have h2 : (2 : ℂ)^(-(2 : ℂ)) = 1/4 := by
    calc
      _ = ((2 : ℂ)^2)⁻¹ := by
        change (2 : ℂ)^(-((2 : ℕ) : ℂ)) = _
        rw [Complex.cpow_neg,Complex.cpow_natCast]
      _ = _ := by norm_num
  apply Complex.ofReal_injective
  rw [spectralKSquareMoment_closed]
  norm_num only [Nat.cast_zero,zero_add,mul_zero,zero_sub,Complex.Gamma_one,div_one]
  rw [h2,hΓ]
  calc
    _ = (1/4 : ℂ)*(Real.pi : ℂ)*
        (Complex.Gamma (1/2-(t : ℂ)*Complex.I)*Complex.Gamma (1/2+(t : ℂ)*Complex.I)) := by ring
    _ = _ := by
      rw [spectral_Gamma_half_imaginary_product,Complex.ofReal_div,Complex.ofReal_pow,
        Complex.ofReal_mul,Complex.ofReal_ofNat]
      ring

end ArtinMatthews
