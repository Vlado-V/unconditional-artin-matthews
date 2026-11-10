module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine one-coordinate Gaussian Poisson identity and absolute convergence.
Reused from OAI/NumberTheory/CubicMoment/Estimates/HuxleyGaussianPoisson.lean
and HuxleyGaussianCoordinates.lean in the local OpenAI math snapshot. Only the
generic real-coordinate lemmas are retained; no Eisenstein-specific premise.
-/
namespace ArtinMatthews
noncomputable section
open Filter Asymptotics MeasureTheory

lemma coordinate_summable_integer_quadratic_exp (A B C : ℂ) (hA : A.re < 0) :
    Summable (fun n : ℤ => Complex.exp (A*(n:ℂ)^2+B*(n:ℂ)+C)) := by
  have hdec := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact hA B (-2)).isBigO
  have hs := summable_of_isBigO (Real.summable_abs_int_rpow (show (1:ℝ) < 2 by norm_num))
    (hdec.comp_tendsto Int.tendsto_coe_cofinite)
  have hm := hs.mul_right (Complex.exp C)
  convert hm using 1
  ext n
  simp only [Function.comp_apply,Complex.ofReal_intCast,← Complex.exp_add]

lemma coordinate_gaussian_poisson {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    (∑' n : ℤ, Complex.exp ((-Real.pi*a*(n:ℝ)^2:ℝ):ℂ)*
      Complex.exp (((2*Real.pi*ξ*(n:ℝ):ℝ):ℂ)*Complex.I)) =
    ((1/Real.sqrt a:ℝ):ℂ)*(∑' m : ℤ,
      Complex.exp ((-Real.pi/a*((m:ℝ)-ξ)^2:ℝ):ℂ)) := by
  have hp : 1/(a:ℂ)^(1/2:ℂ) = ((1/Real.sqrt a:ℝ):ℂ) := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num,
      ← Complex.ofReal_cpow ha.le,← Real.sqrt_eq_rpow,
      Complex.ofReal_div,Complex.ofReal_one]
  calc
    _ = ∑' n : ℤ, Complex.exp (-(Real.pi:ℂ)*(a:ℂ)*(n:ℂ)^2+
        2*(Real.pi:ℂ)*(Complex.I*(ξ:ℂ))*(n:ℂ)) := by
      apply tsum_congr
      intro n
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = _ := by
      rw [Complex.tsum_exp_neg_quadratic (a := (a:ℂ)) (by simpa using ha),hp]
      congr 1
      apply tsum_congr
      intro m
      congr 1
      push_cast
      ring_nf
      norm_num


lemma coordinate_summable_real_gaussian_shift {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    Summable (fun n : ℤ => Real.exp (-Real.pi*a*((n:ℝ)-ξ)^2)) := by
  have h := coordinate_summable_integer_quadratic_exp
    ((-Real.pi*a:ℝ):ℂ) ((2*Real.pi*a*ξ:ℝ):ℂ) ((-Real.pi*a*ξ^2:ℝ):ℂ)
    (by simp only [Complex.ofReal_re]; exact mul_neg_of_neg_of_pos (by linarith [Real.pi_pos]) ha)
  convert (Complex.hasSum_re h.hasSum).summable using 1
  ext n
  rw [← Complex.ofReal_intCast]
  norm_cast
  congr 1
  push_cast
  ring

def coordinateGaussianFactor (a ξ : ℝ) (n : ℤ) : ℂ :=
  Complex.exp ((-Real.pi*a*(n:ℝ)^2:ℝ):ℂ)*
    Complex.exp (((2*Real.pi*ξ*(n:ℝ):ℝ):ℂ)*Complex.I)

lemma norm_coordinateGaussianFactor (a ξ : ℝ) (n : ℤ) :
    ‖coordinateGaussianFactor a ξ n‖ = Real.exp (-Real.pi*a*(n:ℝ)^2) := by
  simp only [coordinateGaussianFactor,norm_mul,Complex.norm_exp,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,
    sub_zero,Real.exp_zero,mul_one]

lemma summable_norm_coordinateGaussianFactor {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    Summable (fun n => ‖coordinateGaussianFactor a ξ n‖) := by
  simp only [norm_coordinateGaussianFactor]
  simpa using coordinate_summable_real_gaussian_shift ha 0

end
end ArtinMatthews
