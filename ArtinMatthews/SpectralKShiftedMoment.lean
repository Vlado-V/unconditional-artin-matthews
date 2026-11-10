module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralBesselProductClosed
public import ArtinMatthews.SpectralBesselProductMellin
public import ArtinMatthews.SpectralKDerivativeAdjacentOrder
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

/-! Exact weighted square moments of the genuine K kernel on a vertical
order line. Conjugation and the four-Gamma Mellin identity retain the
real order shift throughout. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein
open scoped ComplexConjugate

namespace ArtinMatthews

def spectralKShiftedMoment (k : ℕ) (δ t : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ),x^(2*k)*‖schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x‖^2

theorem spectralKShiftedMoment_integrand (k : ℕ) (δ t x : ℝ) (hx : 0 < x) :
    (x : ℂ)^((2*(k : ℂ)+1)-1)*
        schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x*
        schlafliBesselK ((δ : ℂ)-(t : ℂ)*Complex.I) x =
      ((x^(2*k)*‖schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x‖^2 : ℝ) : ℂ) := by
  have hc : star ((δ : ℂ)+(t : ℂ)*Complex.I) = (δ : ℂ)-(t : ℂ)*Complex.I := by
    change conj ((δ : ℂ)+(t : ℂ)*Complex.I) = _
    simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg,sub_eq_add_neg]
  rw [show (2*(k : ℂ)+1)-1 = ((2*k : ℕ) : ℂ) by push_cast;ring,
    Complex.cpow_natCast,← hc,← schlafliBesselK_star_order _ hx,mul_assoc]
  have he (z : ℂ) : z*star z = ((‖z‖^2 : ℝ) : ℂ) := by
    rw [mul_comm]
    change conj z*z = _
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  rw [he]
  push_cast
  rfl

theorem spectralKShiftedMoment_integrable (k : ℕ) (δ t : ℝ)
    (hδ : |δ| < (k : ℝ)+1/2) :
    IntegrableOn (fun x : ℝ => x^(2*k)*‖schlafliBesselK ((δ : ℂ)+(t : ℂ)*Complex.I) x‖^2) (Ioi 0) := by
  have h : |((δ : ℂ)+(t : ℂ)*Complex.I).re|+|((δ : ℂ)-(t : ℂ)*Complex.I).re| <
      (2*(k : ℂ)+1).re := by
    simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,
      Complex.natCast_re,Complex.one_re]
    norm_num
    linarith
  have hi := (schlafliBesselK_product_mellin_integrable_of_re_gt
    ((δ : ℂ)+(t : ℂ)*Complex.I) ((δ : ℂ)-(t : ℂ)*Complex.I) (2*(k : ℂ)+1) h).re
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [spectralKShiftedMoment_integrand k δ t x hx]
  rfl

theorem spectralKShiftedMoment_closed (k : ℕ) (δ t : ℝ)
    (hδ : |δ| < (k : ℝ)+1/2) :
    let a : ℂ := (k : ℂ)+1/2
    let s : ℂ := 2*(k : ℂ)+1
    (spectralKShiftedMoment k δ t : ℂ) =
      (2 : ℂ)^(s-3)*Complex.Gamma (a-δ)*Complex.Gamma (a-(t : ℂ)*Complex.I)*
        Complex.Gamma (a+(t : ℂ)*Complex.I)*Complex.Gamma (a+δ)/Complex.Gamma s := by
  dsimp only
  let a : ℂ := (k : ℂ)+1/2
  let s : ℂ := 2*(k : ℂ)+1
  let ν : ℂ := (δ : ℂ)+(t : ℂ)*Complex.I
  let μ : ℂ := (δ : ℂ)-(t : ℂ)*Complex.I
  have h : |ν.re|+|μ.re| < s.re := by
    dsimp only [ν,μ,s]
    norm_num [Complex.add_re,Complex.sub_re,Complex.mul_re]
    linarith
  have hI : (spectralKShiftedMoment k δ t : ℂ) =
      ∫ x in Ioi (0 : ℝ),(x : ℂ)^(s-1)*schlafliBesselK ν x*schlafliBesselK μ x := by
    unfold spectralKShiftedMoment
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact (spectralKShiftedMoment_integrand k δ t x hx).symm
  rw [hI,schlafliBesselK_product_mellin_closed ν μ s h]
  rw [show (s-ν-μ)/2 = a-δ by dsimp only [s,ν,μ,a];ring,
    show (s+ν-μ)/2 = a+(t : ℂ)*Complex.I by dsimp only [s,ν,μ,a];ring,
    show (s-ν+μ)/2 = a-(t : ℂ)*Complex.I by dsimp only [s,ν,μ,a];ring,
    show (s+ν+μ)/2 = a+δ by dsimp only [s,ν,μ,a];ring]
  ring

end ArtinMatthews
