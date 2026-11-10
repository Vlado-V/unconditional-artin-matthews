module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ArtinMatthews.SpectralGammaReflectionStrip
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The exact Gamma factor which removes the first pair of cosh zeros
from the literal ABL windows. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

def spectralABLCoshCancellation (z : ℂ) : ℂ :=
  Complex.Gamma (3/2+Complex.I*z)*Complex.Gamma (3/2-Complex.I*z)/(Real.pi : ℂ)

theorem spectralABLCoshCancellation_even (z : ℂ) :
    spectralABLCoshCancellation (-z) = spectralABLCoshCancellation z := by
  unfold spectralABLCoshCancellation
  rw [show (3/2 : ℂ)+Complex.I*(-z) = 3/2-Complex.I*z by ring,
    show (3/2 : ℂ)-Complex.I*(-z) = 3/2+Complex.I*z by ring,mul_comm]

theorem spectralABLCoshCancellation_differentiableAt (z : ℂ) (hz : |z.im| < 3/2) :
    DifferentiableAt ℂ spectralABLCoshCancellation z := by
  have hp : 0 < ((3/2 : ℂ)+Complex.I*z).re := by
    norm_num [Complex.mul_re]
    linarith [(abs_lt.mp hz).2]
  have hm : 0 < ((3/2 : ℂ)-Complex.I*z).re := by
    norm_num [Complex.mul_re]
    linarith [(abs_lt.mp hz).1]
  exact (((Complex.hasDerivAt_Gamma_of_re_pos hp).differentiableAt.comp z (by fun_prop)).mul
    ((Complex.hasDerivAt_Gamma_of_re_pos hm).differentiableAt.comp z (by fun_prop))).div_const _

theorem spectralABLCoshCancellation_mul_cosh (z : ℂ) (hz : |z.im| < 1/2) :
    spectralABLCoshCancellation z*Complex.cosh ((Real.pi : ℂ)*z) = z^2+1/4 := by
  let v := Complex.I*z
  have h0 : -(1/2 : ℝ) < v.re := by
    dsimp only [v]
    norm_num [Complex.mul_re]
    linarith [(abs_lt.mp hz).2]
  have h1 : v.re < 1/2 := by
    dsimp only [v]
    norm_num [Complex.mul_re]
    linarith [(abs_lt.mp hz).1]
  have hgp : Complex.Gamma (v+1/2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num;linarith)
  have hvp : (1/2 : ℂ)+v ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  have hvm : (1/2 : ℂ)-v ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  have he := (eq_div_iff hgp).mp (spectral_Gamma_half_cos_reflection v h0 h1)
  have hcos : Complex.cos ((Real.pi : ℂ)*v) = Complex.cosh ((Real.pi : ℂ)*z) := by
    dsimp only [v]
    rw [show (Real.pi : ℂ)*(Complex.I*z) = ((Real.pi : ℂ)*z)*Complex.I by ring,
      Complex.cos_mul_I]
  rw [hcos,show v+1/2 = (1/2 : ℂ)+v by ring] at he
  have hpoly : ((1/2 : ℂ)+v)*((1/2 : ℂ)-v) = z^2+1/4 := by
    dsimp only [v]
    linear_combination -z^2*Complex.I_sq
  unfold spectralABLCoshCancellation
  rw [show (3/2 : ℂ)+Complex.I*z = ((1/2 : ℂ)+v)+1 by dsimp only [v];ring,
    show (3/2 : ℂ)-Complex.I*z = ((1/2 : ℂ)-v)+1 by dsimp only [v];ring,
    Complex.Gamma_add_one _ hvp,Complex.Gamma_add_one _ hvm]
  calc
    _ = (((1/2 : ℂ)+v)*((1/2 : ℂ)-v))*
        ((Complex.Gamma (1/2-v)*Complex.cosh ((Real.pi : ℂ)*z))*Complex.Gamma (1/2+v))/(Real.pi : ℂ) := by ring
    _ = _ := by rw [he,hpoly];field_simp

theorem spectralABLCoshCancellation_half_I :
    spectralABLCoshCancellation (Complex.I/2) = (Real.pi : ℂ)⁻¹ := by
  unfold spectralABLCoshCancellation
  rw [show (3/2 : ℂ)+Complex.I*(Complex.I/2) = 1 by linear_combination Complex.I_sq/2,
    show (3/2 : ℂ)-Complex.I*(Complex.I/2) = 2 by linear_combination -Complex.I_sq/2]
  norm_num

theorem spectralGamma_norm_le_real (z : ℂ) (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz,Complex.GammaIntegral,Real.Gamma_eq_integral hz]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_nonneg _),Complex.norm_cpow_eq_rpow_re_of_pos hx]
  norm_num

theorem spectralABLCoshCancellation_strip_bound (B : ℝ) (hB : 0 ≤ B) (hB' : B < 3/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, |z.im| ≤ B → ‖spectralABLCoshCancellation z‖ ≤ C := by
  have hg : ContinuousOn Real.Gamma (Ioi (0 : ℝ)) := by
    intro x hx
    change 0 < x at hx
    exact (Real.differentiableAt_Gamma (fun n => by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)).continuousAt.continuousWithinAt
  have hc : ContinuousOn Real.Gamma (Icc (3/2-B) (3/2+B)) :=
    hg.mono (fun x hx => by change 0 < x;linarith [hx.1])
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (3/2) ⟨by linarith,by linarith⟩)
  refine ⟨(M+1)^2/Real.pi,by positivity,?_⟩
  intro z hz
  have hp : ((3/2 : ℂ)+Complex.I*z).re ∈ Icc (3/2-B) (3/2+B) := by
    norm_num [Complex.mul_re]
    constructor <;> linarith [(abs_le.mp hz).1,(abs_le.mp hz).2]
  have hm : ((3/2 : ℂ)-Complex.I*z).re ∈ Icc (3/2-B) (3/2+B) := by
    norm_num [Complex.mul_re]
    constructor <;> linarith [(abs_le.mp hz).1,(abs_le.mp hz).2]
  have hb (w : ℂ) (hw : w.re ∈ Icc (3/2-B) (3/2+B)) : ‖Complex.Gamma w‖ ≤ M+1 := by
    have hr : 0 < w.re := by linarith [hw.1]
    have hh : Real.Gamma w.re ≤ M := (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs] using hM w.re hw)
    exact (spectralGamma_norm_le_real w hr).trans (hh.trans (by linarith))
  unfold spectralABLCoshCancellation
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_right
    (by simpa only [pow_two] using mul_le_mul (hb _ hp) (hb _ hm) (norm_nonneg _) (by positivity)) Real.pi_pos.le

end ArtinMatthews
