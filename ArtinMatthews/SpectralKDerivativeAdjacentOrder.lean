module

public import ArtinMatthews.SpectralBesselKEquation
public import ArtinMatthews.SpectralKLRealKernel
public import ArtinMatthews.SpectralBesselKRecurrence
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal derivative of the Schlaefli kernel in adjacent orders,
and the real imaginary-order derivative estimate used in the height frame. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology ComplexConjugate

namespace ArtinMatthews

theorem schlafliBesselK_even_order (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    schlafliBesselK (-ν) x = schlafliBesselK ν x := by
  rw [schlafliBesselK_cosh_integral _ hx,schlafliBesselK_cosh_integral _ hx]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  simp only [spectralKCoshKernel,neg_mul,Complex.cosh_neg]

theorem schlafliBesselK_star_order (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    star (schlafliBesselK ν x) = schlafliBesselK (star ν) x := by
  rw [schlafliBesselK_cosh_integral _ hx,schlafliBesselK_cosh_integral _ hx]
  change conj (∫ u in Ioi (0 : ℝ), spectralKCoshKernel ν x u) = _
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  dsimp only [spectralKCoshKernel]
  rw [map_mul,← Complex.exp_conj,Complex.conj_ofReal,← Complex.cosh_conj,map_mul,Complex.conj_ofReal]
  rfl

theorem spectralSchlafliPrefactor_lower_order (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    spectralSchlafliPrefactor (ν-1) x = ((x : ℂ)/2)*spectralSchlafliPrefactor ν x := by
  have hx0 : (x : ℂ)/2 ≠ 0 := div_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne') (by norm_num)
  unfold spectralSchlafliPrefactor
  rw [show -(ν-1) = -ν+1 by ring,Complex.cpow_add _ _ hx0,Complex.cpow_one]
  ring

theorem schlafliBesselK_order_recurrence (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    schlafliBesselK (ν+1) x = schlafliBesselK (ν-1) x+(2*ν/(x : ℂ))*schlafliBesselK ν x := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hp := spectralSchlafliPrefactor_lower_order (ν+1) hx
  rw [add_sub_cancel_right] at hp
  have hplus : spectralSchlafliPrefactor (ν+1) x = (2/(x : ℂ))*spectralSchlafliPrefactor ν x := by
    field_simp [hx0]
    linear_combination -2*hp
  change spectralSchlafliPrefactor (ν+1) x*schlafliIntegral (ν+1) x =
    spectralSchlafliPrefactor (ν-1) x*schlafliIntegral (ν-1) x+
      (2*ν/(x : ℂ))*(spectralSchlafliPrefactor ν x*schlafliIntegral ν x)
  rw [schlafliIntegral_recurrence ν x hx,hplus,spectralSchlafliPrefactor_lower_order ν hx]
  field_simp [hx0]
  ring

theorem schlafliBesselK_deriv_adjacent_order (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    deriv (schlafliBesselK ν) x = -(1/2 : ℂ)*(schlafliBesselK (ν-1) x+schlafliBesselK (ν+1) x) := by
  rw [schlafliBesselK_deriv ν x hx,schlafliIntegral_deriv ν x hx,schlafliBesselK_order_recurrence ν hx]
  change spectralSchlafliPrefactor ν x*
      (-((x : ℂ)/2)*schlafliIntegral (ν-1) x-ν/(x : ℂ)*schlafliIntegral ν x) =
    -(1/2 : ℂ)*(spectralSchlafliPrefactor (ν-1) x*schlafliIntegral (ν-1) x+
      (spectralSchlafliPrefactor (ν-1) x*schlafliIntegral (ν-1) x+
        (2*ν/(x : ℂ))*(spectralSchlafliPrefactor ν x*schlafliIntegral ν x)))
  rw [spectralSchlafliPrefactor_lower_order ν hx]
  ring

theorem spectralKLRealKernel_hasDerivAt_re (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (spectralKLRealKernel t)
      ((deriv (schlafliBesselK ((t : ℂ)*Complex.I)) x).re) x := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    ((schlafliBesselK_hasDerivAt ((t : ℂ)*Complex.I) x hx).differentiableAt.hasDerivAt)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  change spectralKLRealKernel t y = (schlafliBesselK ((t : ℂ)*Complex.I) y).re
  rw [schlafliBesselK_imaginary_eq_realKernel t hy,Complex.ofReal_re]

theorem spectralKLRealKernel_deriv_norm_le_adjacent (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖deriv (spectralKLRealKernel t) x‖ ≤ ‖schlafliBesselK (1+(t : ℂ)*Complex.I) x‖ := by
  let ν := (t : ℂ)*Complex.I
  have hν : star (1+ν) = 1-ν := by
    change conj (1+(t : ℂ)*Complex.I) = 1-(t : ℂ)*Complex.I
    simp only [map_add,map_one,map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg,sub_eq_add_neg]
  have hneg : schlafliBesselK (ν-1) x = star (schlafliBesselK (1+ν) x) := by
    rw [schlafliBesselK_star_order _ hx,hν,
      show ν-1=-(1-ν) by ring,schlafliBesselK_even_order _ hx]
  rw [(spectralKLRealKernel_hasDerivAt_re t hx).deriv,Real.norm_eq_abs]
  refine (Complex.abs_re_le_norm _).trans ?_
  change ‖deriv (schlafliBesselK ν) x‖ ≤ _
  rw [schlafliBesselK_deriv_adjacent_order ν hx,hneg,add_comm ν 1,norm_mul]
  calc
    _ ≤ ‖(-(1/2) : ℂ)‖*(‖star (schlafliBesselK (1+ν) x)‖+‖schlafliBesselK (1+ν) x‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = _ := by simp only [norm_star]; norm_num; ring

end ArtinMatthews
