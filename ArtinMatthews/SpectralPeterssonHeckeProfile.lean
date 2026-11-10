module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
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

/-! The rescaled horizontal profile of the weight-two Hecke summand.
Its first two derivatives admit integrable envelopes uniformly for
regulator in [0,1] and bounded nonnegative exponential parameter. -/

noncomputable section
open MeasureTheory Set

namespace ArtinMatthews

private def heckeProfileZ (x : ℝ) : ℂ := (x : ℂ)+Complex.I
private def heckeProfileR (x : ℝ) : ℝ := 1+x^2

private theorem heckeProfileZ_norm_sq (x : ℝ) : ‖heckeProfileZ x‖^2 = heckeProfileR x := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply,heckeProfileZ,heckeProfileR,pow_two,add_comm]

private theorem heckeProfileZ_one_le (x : ℝ) : 1 ≤ ‖heckeProfileZ x‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [heckeProfileZ_norm_sq]
  unfold heckeProfileR
  nlinarith

private theorem heckeProfileZ_ne (x : ℝ) : heckeProfileZ x ≠ 0 :=
  norm_pos_iff.mp (zero_lt_one.trans_le (heckeProfileZ_one_le x))

private theorem heckeProfileR_pos (x : ℝ) : 0 < heckeProfileR x := by
  unfold heckeProfileR
  positivity

private theorem heckeProfileZ_deriv (x : ℝ) : HasDerivAt heckeProfileZ 1 x := by
  have h := (hasDerivAt_id x).ofReal_comp.add (hasDerivAt_const x Complex.I)
  change HasDerivAt (fun y : ℝ => (y : ℂ)+Complex.I) (((1 : ℝ) : ℂ)+0) x at h
  unfold heckeProfileZ
  simpa only [Complex.ofReal_one,add_zero] using h

private theorem heckeProfileR_deriv (x : ℝ) : HasDerivAt heckeProfileR (2*x) x := by
  have h := (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2)
  change HasDerivAt (fun y : ℝ => 1+y^2) (0+(2 : ℝ)*x^(2-1)*1) x at h
  unfold heckeProfileR
  simpa only [zero_add,mul_one,Nat.reduceSub,pow_one] using h

def spectralPeterssonHeckeProfile (u lam x : ℝ) : ℂ :=
  Complex.exp (-Complex.I*(lam : ℂ)/heckeProfileZ x)*(heckeProfileZ x^2)⁻¹*
    ((heckeProfileR x^(-u) : ℝ) : ℂ)

private def heckeProfileLogDeriv (u lam x : ℝ) : ℂ :=
  Complex.I*(lam : ℂ)/(heckeProfileZ x^2)-2/heckeProfileZ x-
    ((2*u*x/heckeProfileR x : ℝ) : ℂ)

private def heckeProfileLogDerivPrime (u lam x : ℝ) : ℂ :=
  -2*Complex.I*(lam : ℂ)/(heckeProfileZ x^3)+2/(heckeProfileZ x^2)-
    ((2*u/heckeProfileR x : ℝ) : ℂ)+((4*u*x^2/(heckeProfileR x)^2 : ℝ) : ℂ)

def spectralPeterssonHeckeProfileFirst (u lam x : ℝ) : ℂ :=
  spectralPeterssonHeckeProfile u lam x*heckeProfileLogDeriv u lam x

def spectralPeterssonHeckeProfileSecond (u lam x : ℝ) : ℂ :=
  spectralPeterssonHeckeProfile u lam x*(heckeProfileLogDeriv u lam x^2+heckeProfileLogDerivPrime u lam x)

theorem spectralPeterssonHeckeProfile_hasDerivAt (u lam x : ℝ) :
    HasDerivAt (spectralPeterssonHeckeProfile u lam) (spectralPeterssonHeckeProfileFirst u lam x) x := by
  let w := heckeProfileZ x
  let R := heckeProfileR x
  have hw : w ≠ 0 := heckeProfileZ_ne x
  have hR : 0 < R := heckeProfileR_pos x
  have hZ := heckeProfileZ_deriv x
  have hW : HasDerivAt (fun t => (heckeProfileZ t^2)⁻¹) (-(2*w)/(w^2)^2) x := by
    dsimp only [w]
    simpa only [Pi.pow_apply,zero_mul,sub_zero,zero_sub,one_mul,Nat.cast_ofNat,Nat.reduceSub,
      pow_one,mul_one,one_div] using
      ((hasDerivAt_const x (1 : ℂ)).fun_div (hZ.pow 2) (pow_ne_zero 2 hw))
  have hExp := ((hasDerivAt_const x (-Complex.I*(lam : ℂ))).fun_div hZ hw).cexp
  have hP : HasDerivAt (fun t => ((heckeProfileR t^(-u) : ℝ) : ℂ))
      ((2*x*(-u)*R^(-u-1) : ℝ) : ℂ) x :=
    ((heckeProfileR_deriv x).rpow_const (p := -u) (Or.inl hR.ne')).ofReal_comp
  apply ((hExp.fun_mul hW).fun_mul hP).congr_deriv
  simp only [spectralPeterssonHeckeProfileFirst,spectralPeterssonHeckeProfile,heckeProfileLogDeriv]
  dsimp only [w,R] at *
  rw [Real.rpow_sub hR,Real.rpow_one]
  push_cast
  field_simp [hw,hR.ne']
  <;> ring

private theorem heckeProfileLogDeriv_hasDerivAt (u lam x : ℝ) :
    HasDerivAt (heckeProfileLogDeriv u lam) (heckeProfileLogDerivPrime u lam x) x := by
  let w := heckeProfileZ x
  let R := heckeProfileR x
  have hw : w ≠ 0 := heckeProfileZ_ne x
  have hR : 0 < R := heckeProfileR_pos x
  have hZ := heckeProfileZ_deriv x
  have h1 := (hasDerivAt_const x (Complex.I*(lam : ℂ))).fun_div (hZ.pow 2) (pow_ne_zero 2 hw)
  have h2 := (hasDerivAt_const x (2 : ℂ)).fun_div hZ hw
  have h3 := (((hasDerivAt_id x).const_mul (2*u)).fun_div (heckeProfileR_deriv x) hR.ne').ofReal_comp
  apply ((h1.sub h2).sub h3).congr_deriv
  unfold heckeProfileLogDerivPrime
  dsimp only [w,R,Pi.pow_apply,id_eq] at *
  push_cast
  field_simp [hw,hR.ne']
  <;> ring

theorem spectralPeterssonHeckeProfileFirst_hasDerivAt (u lam x : ℝ) :
    HasDerivAt (spectralPeterssonHeckeProfileFirst u lam) (spectralPeterssonHeckeProfileSecond u lam x) x := by
  apply ((spectralPeterssonHeckeProfile_hasDerivAt u lam x).fun_mul
    (heckeProfileLogDeriv_hasDerivAt u lam x)).congr_deriv
  unfold spectralPeterssonHeckeProfileFirst spectralPeterssonHeckeProfileSecond
  ring

theorem spectralPeterssonHeckeProfile_norm_le (u lam x : ℝ) (hu : 0 ≤ u) (hlam : 0 ≤ lam) :
    ‖spectralPeterssonHeckeProfile u lam x‖ ≤ (1+x^2)⁻¹ := by
  have hR : 1 ≤ heckeProfileR x := by unfold heckeProfileR; linarith [sq_nonneg x]
  have hE : ‖Complex.exp (-Complex.I*(lam : ℂ)/heckeProfileZ x)‖ ≤ 1 := by
    rw [Complex.norm_exp,Real.exp_le_one_iff,Complex.div_re]
    have h := (Complex.sq_norm (heckeProfileZ x)).symm.trans (heckeProfileZ_norm_sq x)
    rw [h]
    simp [heckeProfileZ,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam) (heckeProfileR_pos x).le
  have huR : heckeProfileR x^(-u) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (neg_nonpos.mpr hu)
  unfold spectralPeterssonHeckeProfile
  rw [norm_mul,norm_mul,norm_inv,norm_pow,heckeProfileZ_norm_sq,Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (heckeProfileR_pos x).le _)]
  calc
    _ ≤ (1*(heckeProfileR x)⁻¹)*1 := by gcongr
    _ = _ := by simp [heckeProfileR]

private theorem heckeProfile_xRatio_norm_le (x : ℝ) : ‖x/heckeProfileR x‖ ≤ 1 := by
  have h : |x| ≤ heckeProfileR x := by
    unfold heckeProfileR
    nlinarith [sq_abs x,sq_nonneg (|x|-1)]
  rw [norm_div,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (heckeProfileR_pos x)]
  exact (div_le_one (heckeProfileR_pos x)).mpr h

private theorem heckeProfileLogDeriv_norm_le (u lam x : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hlam : 0 ≤ lam) :
    ‖heckeProfileLogDeriv u lam x‖ ≤ lam+4 := by
  have hw := heckeProfileZ_one_le x
  have h₁ : ‖Complex.I*(lam : ℂ)/(heckeProfileZ x^2)‖ ≤ lam := by
    rw [norm_div,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_of_nonneg hlam,norm_pow]
    exact div_le_self hlam (one_le_pow₀ hw)
  have h₂ : ‖(2 : ℂ)/heckeProfileZ x‖ ≤ 2 := by
    rw [norm_div,show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact div_le_self (by norm_num) hw
  have h₃ : ‖((2*u*x/heckeProfileR x : ℝ) : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real,mul_div_assoc,norm_mul,Real.norm_of_nonneg (mul_nonneg zero_le_two hu.1)]
    nlinarith [mul_le_mul_of_nonneg_left (heckeProfile_xRatio_norm_le x) (mul_nonneg zero_le_two hu.1),hu.2]
  have h₁₂ := norm_sub_le (Complex.I*(lam : ℂ)/(heckeProfileZ x^2)) ((2 : ℂ)/heckeProfileZ x)
  unfold heckeProfileLogDeriv
  exact (norm_sub_le _ _).trans (by linarith)

private theorem heckeProfileLogDerivPrime_norm_le (u lam x : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) (hlam : 0 ≤ lam) : ‖heckeProfileLogDerivPrime u lam x‖ ≤ 2*lam+8 := by
  have hw := heckeProfileZ_one_le x
  have hR : 1 ≤ heckeProfileR x := by unfold heckeProfileR; linarith [sq_nonneg x]
  have h₁ : ‖-2*Complex.I*(lam : ℂ)/(heckeProfileZ x^3)‖ ≤ 2*lam := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
      Real.norm_of_nonneg hlam,norm_pow,show ‖(-2 : ℂ)‖ = 2 by norm_num]
    exact div_le_self (by positivity) (one_le_pow₀ hw)
  have h₂ : ‖(2 : ℂ)/(heckeProfileZ x^2)‖ ≤ 2 := by
    rw [norm_div,norm_pow,show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact div_le_self (by norm_num) (one_le_pow₀ hw)
  have h₃ : ‖((2*u/heckeProfileR x : ℝ) : ℂ)‖ ≤ 2 := by
    have hnum : 0 ≤ 2*u := mul_nonneg zero_le_two hu.1
    rw [Complex.norm_real,Real.norm_of_nonneg (div_nonneg hnum (heckeProfileR_pos x).le)]
    exact (div_le_self hnum hR).trans (by linarith [hu.2])
  have h₄ : ‖((4*u*x^2/(heckeProfileR x)^2 : ℝ) : ℂ)‖ ≤ 4 := by
    rw [Complex.norm_real,mul_div_assoc,← div_pow,norm_mul,norm_pow,
      Real.norm_of_nonneg (mul_nonneg (by norm_num) hu.1)]
    have hsq : ‖x/heckeProfileR x‖^2 ≤ 1 := by
      simpa using pow_le_pow_left₀ (norm_nonneg _) (heckeProfile_xRatio_norm_le x) 2
    nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hu.1),hu.2]
  have h₁₂ := norm_add_le (-2*Complex.I*(lam : ℂ)/(heckeProfileZ x^3)) (2/(heckeProfileZ x^2))
  have h₁₂₃ := norm_sub_le (-2*Complex.I*(lam : ℂ)/(heckeProfileZ x^3)+2/(heckeProfileZ x^2))
    ((2*u/heckeProfileR x : ℝ) : ℂ)
  unfold heckeProfileLogDerivPrime
  exact (norm_add_le _ _).trans (by linarith)

theorem spectralPeterssonHeckeProfileFirst_norm_le (u lam x : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) (hlam : 0 ≤ lam) :
    ‖spectralPeterssonHeckeProfileFirst u lam x‖ ≤ (1+x^2)⁻¹*(lam+4) := by
  rw [spectralPeterssonHeckeProfileFirst,norm_mul]
  exact mul_le_mul (spectralPeterssonHeckeProfile_norm_le u lam x hu.1 hlam)
    (heckeProfileLogDeriv_norm_le u lam x hu hlam) (norm_nonneg _) (by positivity)

theorem spectralPeterssonHeckeProfileSecond_norm_le (u lam x : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) (hlam : 0 ≤ lam) :
    ‖spectralPeterssonHeckeProfileSecond u lam x‖ ≤ (1+x^2)⁻¹*((lam+4)^2+2*lam+8) := by
  rw [spectralPeterssonHeckeProfileSecond,norm_mul]
  refine mul_le_mul (spectralPeterssonHeckeProfile_norm_le u lam x hu.1 hlam) ?_ (norm_nonneg _) (by positivity)
  refine (norm_add_le _ _).trans ?_
  rw [norm_pow]
  linarith [pow_le_pow_left₀ (norm_nonneg (heckeProfileLogDeriv u lam x))
    (heckeProfileLogDeriv_norm_le u lam x hu hlam) 2,
    heckeProfileLogDerivPrime_norm_le u lam x hu hlam]

theorem spectralPeterssonHeckeProfile_eq (u lam x : ℝ) :
    spectralPeterssonHeckeProfile u lam x =
      Complex.exp (-Complex.I*(lam : ℂ)/((x : ℂ)+Complex.I))*(((x : ℂ)+Complex.I)^2)⁻¹*
        (((1+x^2)^(-u) : ℝ) : ℂ) := rfl

theorem spectralPeterssonHeckeProfileSecond_measurable (u lam : ℝ) :
    Measurable (spectralPeterssonHeckeProfileSecond u lam) := by
  unfold spectralPeterssonHeckeProfileSecond spectralPeterssonHeckeProfile
    heckeProfileLogDeriv heckeProfileLogDerivPrime heckeProfileR heckeProfileZ
  measurability

end ArtinMatthews
