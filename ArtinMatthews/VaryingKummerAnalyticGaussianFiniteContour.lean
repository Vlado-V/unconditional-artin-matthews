module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial


set_option backward.privateInPublic true
@[expose] public section

/-! A finite rectangle identity. Neither the horizontal integrals nor the
right-line tails are discarded. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Set Complex Metric
open scoped Topology
noncomputable section

def finiteVerticalIntegral (F : ℂ → ℂ) (a T : ℝ) : ℂ :=
  ∫ y in -T..T, F ((a : ℂ)+(y : ℂ)*I)

def finiteHorizontalIntegral (F : ℂ → ℂ) (a b y : ℝ) : ℂ :=
  ∫ x in a..b, F ((x : ℂ)+(y : ℂ)*I)

def finiteHorizontalError (F : ℂ → ℂ) (a b T : ℝ) : ℂ :=
  I*(finiteHorizontalIntegral F a b (-T)-finiteHorizontalIntegral F a b T)

def rightVerticalTail (F : ℂ → ℂ) (b T : ℝ) : ℂ :=
  ∫ y in (Ioc (-T) T)ᶜ, F ((b : ℂ)+(y : ℂ)*I)

theorem finite_vertical_shift (F : ℂ → ℂ) {a b T : ℝ}
    (hab : a ≤ b) (hT : 0 ≤ T)
    (hF : DifferentiableOn ℂ F {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ |z.im| ≤ T}) :
    finiteVerticalIntegral F b T = finiteVerticalIntegral F a T + finiteHorizontalError F a b T := by
  have H := integral_boundary_rect_eq_zero_of_differentiableOn F
    ((a : ℂ)+(-T : ℝ)*I) ((b : ℂ)+(T : ℂ)*I) (hF.mono (by
      intro z hz
      have hre := hz.1
      have him := hz.2
      simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,mul_zero,I_im,mul_one,
        sub_zero,add_zero,add_im,mul_im,zero_add] at hre him
      rw [uIcc_of_le hab] at hre
      rw [uIcc_of_le (show -T ≤ T by linarith)] at him
      exact ⟨hre.1,hre.2,abs_le.mpr him⟩))
  simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,mul_zero,I_im,mul_one,
    sub_zero,add_zero,add_im,mul_im,zero_add,smul_eq_mul] at H
  change finiteHorizontalIntegral F a b (-T)-finiteHorizontalIntegral F a b T+
    I*finiteVerticalIntegral F b T-I*finiteVerticalIntegral F a T=0 at H
  have HH := congrArg (fun z : ℂ => I*z) H
  simp only [mul_add,mul_sub,← mul_assoc,I_mul_I,neg_one_mul,mul_zero] at HH
  dsimp only [finiteHorizontalError]
  linear_combination -HH

theorem full_vertical_eq_finite_add_tail (F : ℂ → ℂ) {b T : ℝ} (hT : 0 ≤ T)
    (hF : Integrable (fun y : ℝ => F ((b : ℂ)+(y : ℂ)*I))) :
    (∫ y : ℝ, F ((b : ℂ)+(y : ℂ)*I)) = finiteVerticalIntegral F b T+rightVerticalTail F b T := by
  have H := integral_add_compl (s := Ioc (-T) T) measurableSet_Ioc hF
  rw [← intervalIntegral.integral_of_le (show -T ≤ T by linarith)] at H
  exact H.symm

theorem full_vertical_finite_shift (F : ℂ → ℂ) {a b T : ℝ}
    (hab : a ≤ b) (hT : 0 ≤ T)
    (hF : DifferentiableOn ℂ F {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ |z.im| ≤ T})
    (hi : Integrable (fun y : ℝ => F ((b : ℂ)+(y : ℂ)*I))) :
    (∫ y : ℝ, F ((b : ℂ)+(y : ℂ)*I)) =
      finiteVerticalIntegral F a T+finiteHorizontalError F a b T+rightVerticalTail F b T := by
  rw [full_vertical_eq_finite_add_tail F hT hi,finite_vertical_shift F hab hT hF]

end
end ArtinMatthews.VaryingKummerAnalytic
