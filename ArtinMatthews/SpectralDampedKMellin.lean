module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralDampedKMellinKernel
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

/-! The actual Mellin transform of exp(-x)K_nu(x), obtained by absolute
Laplace/cosh Fubini and the proved beta log integral. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralDampedK_mellin_integrable (ν s : ℂ) (hs : |ν.re| < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^(s-1)*Complex.exp (-(x : ℂ))*schlafliBesselK ν x)
      (Ioi (0 : ℝ)) := by
  have hi := (spectralDampedKMellinKernel_integrable ν s hs).integral_prod_right
  apply (hi.const_mul (1/2 : ℂ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [spectralDampedKMellinKernel_integral_u ν s hx]
  ring_nf

theorem spectralDampedK_mellin_beta (ν s : ℂ) (hs : |ν.re| < s.re) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*Complex.exp (-(x : ℂ))*schlafliBesselK ν x) =
      (1/2 : ℂ)*Complex.Gamma s*(2 : ℂ)^s*Complex.betaIntegral (s+ν) (s-ν) := by
  have hs0 : 0 < s.re := (abs_nonneg ν.re).trans_lt hs
  have h := integral_integral_swap (f := fun u x : ℝ => spectralDampedKMellinKernel ν s u x)
    (spectralDampedKMellinKernel_integrable ν s hs)
  have hleft : (∫ u : ℝ, ∫ x in Ioi (0 : ℝ), spectralDampedKMellinKernel ν s u x) =
      Complex.Gamma s*(2 : ℂ)^s*Complex.betaIntegral (s+ν) (s-ν) := by
    simp_rw [spectralDampedKMellinKernel_integral_x ν s hs0]
    rw [integral_const_mul,spectralCoshBetaProfile_integral]
    ring_nf
  have hright : (∫ x in Ioi (0 : ℝ), ∫ u : ℝ, spectralDampedKMellinKernel ν s u x) =
      2*(∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*Complex.exp (-(x : ℂ))*schlafliBesselK ν x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact spectralDampedKMellinKernel_integral_u ν s hx
  rw [hleft,hright] at h
  linear_combination -h/2

theorem spectralDampedK_mellin (ν s : ℂ) (hs : |ν.re| < s.re) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*Complex.exp (-(x : ℂ))*schlafliBesselK ν x) =
      (Real.sqrt Real.pi : ℂ)*(2 : ℂ)^(-s)*Complex.Gamma (s+ν)*Complex.Gamma (s-ν)/Complex.Gamma (s+1/2) := by
  have hs0 : 0 < s.re := (abs_nonneg ν.re).trans_lt hs
  have ha : 0 < (s+ν).re := by simp only [Complex.add_re]; linarith [neg_le_abs ν.re]
  have hb : 0 < (s-ν).re := by simp only [Complex.sub_re]; linarith [le_abs_self ν.re]
  have hG2 : Complex.Gamma (2*s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using mul_pos two_pos hs0)
  have hGh : Complex.Gamma (s+1/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num; linarith)
  have hdup := Complex.Gamma_mul_Gamma_add_half s
  have hratio : Complex.Gamma s/Complex.Gamma (2*s) =
      (2 : ℂ)^(1-2*s)*(Real.sqrt Real.pi : ℂ)/Complex.Gamma (s+1/2) := by
    apply (div_eq_div_iff hG2 hGh).mpr
    rw [hdup]
    ring_nf
  have hp : (1/2 : ℂ)*(2 : ℂ)^s*(2 : ℂ)^(1-2*s) = (2 : ℂ)^(-s) := by
    rw [mul_assoc,← Complex.cpow_add _ _ (by norm_num),show s+(1-2*s) = 1+(-s) by ring,
      Complex.cpow_add _ _ (by norm_num),Complex.cpow_one]
    ring_nf
  rw [spectralDampedK_mellin_beta ν s hs,Complex.betaIntegral_eq_Gamma_mul_div _ _ ha hb,
    show s+ν+(s-ν) = 2*s by ring]
  calc
    _ = ((1/2 : ℂ)*(2 : ℂ)^s)*(Complex.Gamma s/Complex.Gamma (2*s))*
        Complex.Gamma (s+ν)*Complex.Gamma (s-ν) := by ring_nf
    _ = _ := by
      rw [hratio]
      linear_combination (Complex.Gamma (s+ν)*Complex.Gamma (s-ν)*(Real.sqrt Real.pi : ℂ)/Complex.Gamma (s+1/2))*hp

end ArtinMatthews
