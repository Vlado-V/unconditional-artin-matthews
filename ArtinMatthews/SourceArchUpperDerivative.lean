module

public import ArtinMatthews.SourceArchUpperLogDerivative


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

def sourceArchUpperSection (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  sourceArchSphericalGL s (g * sourceKPUpperMatrix ℂ ((t : ℂ)*z))

def sourceArchUpperSectionOne (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  ((2*s+1)*(sourceArchUpperLogOne g z t : ℂ)) * sourceArchUpperSection s g z t

def sourceArchUpperSectionTwo (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  ((2*s+1)^2*(sourceArchUpperLogOne g z t : ℂ)^2 +
    (2*s+1)*(sourceArchUpperLogTwo g z t : ℂ)) * sourceArchUpperSection s g z t

theorem sourceArchUpperSection_eq_exp (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    sourceArchUpperSection s g z t =
      Complex.exp ((sourceArchUpperLog g z t : ℂ)*(2*s+1)) := by
  rw [sourceArchUpperSection, sourceArchSphericalGL,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (sourceArchHeight_pos _).ne'),
    ← Complex.ofReal_log (sourceArchHeight_pos _).le, ← sourceArchUpperLog_eq]

theorem sourceArchUpperSection_hasDerivAt (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    HasDerivAt (sourceArchUpperSection s g z) (sourceArchUpperSectionOne s g z t) t := by
  have h := ((sourceArchUpperLog_hasDerivAt g z t).ofReal_comp.mul_const (2*s+1)).cexp
  convert h using 1
  · funext x
    exact sourceArchUpperSection_eq_exp s g z x
  · rw [sourceArchUpperSectionOne, sourceArchUpperSection_eq_exp]
    ring

theorem sourceArchUpperSectionOne_hasDerivAt (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    HasDerivAt (sourceArchUpperSectionOne s g z) (sourceArchUpperSectionTwo s g z t) t := by
  have h := ((sourceArchUpperLogOne_hasDerivAt g z t).ofReal_comp.const_mul (2*s+1)).mul
    (sourceArchUpperSection_hasDerivAt s g z t)
  convert h using 1
  · rfl
  · unfold sourceArchUpperSectionTwo sourceArchUpperSectionOne
    ring

theorem sourceArchUpperSection_deriv (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    deriv (sourceArchUpperSection s g z) t = sourceArchUpperSectionOne s g z t :=
  (sourceArchUpperSection_hasDerivAt s g z t).deriv

theorem sourceArchUpperSection_deriv_two (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    deriv (deriv (sourceArchUpperSection s g z)) t = sourceArchUpperSectionTwo s g z t := by
  have h : deriv (sourceArchUpperSection s g z) = sourceArchUpperSectionOne s g z :=
    funext (sourceArchUpperSection_deriv s g z)
  rw [h]
  exact (sourceArchUpperSectionOne_hasDerivAt s g z t).deriv

theorem sourceArchUpperSectionOne_bound (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    ‖sourceArchUpperSectionOne s g z t‖ ≤
      ‖2*s+1‖*‖z‖*‖sourceArchUpperSection s g z t‖ := by
  rw [sourceArchUpperSectionOne, norm_mul, norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sourceArchUpperLogOne_bound g z t) (norm_nonneg _)) (norm_nonneg _)

theorem sourceArchUpperSectionTwo_bound (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    ‖sourceArchUpperSectionTwo s g z t‖ ≤
      (‖2*s+1‖^2+3*‖2*s+1‖)*‖z‖^2*‖sourceArchUpperSection s g z t‖ := by
  have h1 := sourceArchUpperLogOne_bound g z t
  have h2 := sourceArchUpperLogTwo_bound g z t
  have hcoef : ‖(2*s+1)^2*(sourceArchUpperLogOne g z t : ℂ)^2 +
      (2*s+1)*(sourceArchUpperLogTwo g z t : ℂ)‖ ≤ (‖2*s+1‖^2+3*‖2*s+1‖)*‖z‖^2 := by
    calc
      _ ≤ ‖(2*s+1)^2*(sourceArchUpperLogOne g z t : ℂ)^2‖ +
          ‖(2*s+1)*(sourceArchUpperLogTwo g z t : ℂ)‖ := norm_add_le _ _
      _ = ‖2*s+1‖^2*|sourceArchUpperLogOne g z t|^2 +
          ‖2*s+1‖*|sourceArchUpperLogTwo g z t| := by
        simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖2*s+1‖^2*‖z‖^2 + ‖2*s+1‖*(3*‖z‖^2) := by gcongr
      _ = _ := by ring
  rw [sourceArchUpperSectionTwo, norm_mul]
  exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)

theorem sourceArchUpperSection_deriv_bound (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    ‖deriv (sourceArchUpperSection s g z) t‖ ≤
      ‖2*s+1‖*‖z‖*‖sourceArchUpperSection s g z t‖ := by
  rw [sourceArchUpperSection_deriv]
  exact sourceArchUpperSectionOne_bound s g z t

theorem sourceArchUpperSection_deriv_two_bound (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ) (t : ℝ) :
    ‖deriv (deriv (sourceArchUpperSection s g z)) t‖ ≤
      (‖2*s+1‖^2+3*‖2*s+1‖)*‖z‖^2*‖sourceArchUpperSection s g z t‖ := by
  rw [sourceArchUpperSection_deriv_two]
  exact sourceArchUpperSectionTwo_bound s g z t

end
end ArtinMatthews.SourceArchJacquet
