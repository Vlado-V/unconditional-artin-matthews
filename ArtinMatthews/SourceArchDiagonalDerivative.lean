module

public import ArtinMatthews.SourceArchDiagonalLog


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

def sourceArchDiagonalSection (s : ℂ) (g : GL (Fin 2) ℂ) (t : ℝ) : ℂ :=
  sourceArchSphericalGL s (g * sourceArchPositiveDiagonal t)

def sourceArchDiagonalSectionOne (s : ℂ) (g : GL (Fin 2) ℂ) (t : ℝ) : ℂ :=
  ((2*s+1)*(sourceArchDiagonalLogOne g t : ℂ)) * sourceArchDiagonalSection s g t

def sourceArchDiagonalSectionTwo (s : ℂ) (g : GL (Fin 2) ℂ) (t : ℝ) : ℂ :=
  ((2*s+1)^2*(sourceArchDiagonalLogOne g t : ℂ)^2 +
    (2*s+1)*(sourceArchDiagonalLogTwo g t : ℂ)) * sourceArchDiagonalSection s g t

theorem sourceArchDiagonalSection_eq_exp (s : ℂ) (g : GL (Fin 2) ℂ) (t : ℝ) :
    sourceArchDiagonalSection s g t =
      Complex.exp ((sourceArchDiagonalLog g t : ℂ)*(2*s+1)) := by
  rw [sourceArchDiagonalSection, sourceArchSphericalGL,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (sourceArchHeight_pos _).ne'),
    ← Complex.ofReal_log (sourceArchHeight_pos _).le, ← sourceArchDiagonalLog_eq]

theorem sourceArchDiagonalSection_hasDerivAt (s : ℂ) (g : GL (Fin 2) ℂ) (t : ℝ) :
    HasDerivAt (sourceArchDiagonalSection s g) (sourceArchDiagonalSectionOne s g t) t := by
  have h := ((sourceArchDiagonalLog_hasDerivAt g t).ofReal_comp.mul_const (2*s+1)).cexp
  convert h using 1
  · funext x
    exact sourceArchDiagonalSection_eq_exp s g x
  · rw [sourceArchDiagonalSectionOne, sourceArchDiagonalSection_eq_exp]
    ring

theorem sourceArchDiagonalSectionOne_hasDerivAt (s : ℂ) (g : GL (Fin 2) ℂ) (t : ℝ) :
    HasDerivAt (sourceArchDiagonalSectionOne s g) (sourceArchDiagonalSectionTwo s g t) t := by
  have h := ((sourceArchDiagonalLogOne_hasDerivAt g t).ofReal_comp.const_mul (2*s+1)).mul
    (sourceArchDiagonalSection_hasDerivAt s g t)
  convert h using 1
  · rfl
  · unfold sourceArchDiagonalSectionTwo sourceArchDiagonalSectionOne
    ring

theorem sourceArchDiagonalSection_deriv (s : ℂ) (g : GL (Fin 2) ℂ) (t : ℝ) :
    deriv (sourceArchDiagonalSection s g) t = sourceArchDiagonalSectionOne s g t :=
  (sourceArchDiagonalSection_hasDerivAt s g t).deriv

theorem sourceArchDiagonalSection_deriv_two (s : ℂ) (g : GL (Fin 2) ℂ) (t : ℝ) :
    deriv (deriv (sourceArchDiagonalSection s g)) t = sourceArchDiagonalSectionTwo s g t := by
  have h : deriv (sourceArchDiagonalSection s g) = sourceArchDiagonalSectionOne s g :=
    funext (sourceArchDiagonalSection_deriv s g)
  rw [h]
  exact (sourceArchDiagonalSectionOne_hasDerivAt s g t).deriv

theorem sourceArchDiagonalSectionOne_bound (s : ℂ) (g : GL (Fin 2) ℂ) (t : ℝ) :
    ‖sourceArchDiagonalSectionOne s g t‖ ≤
      ‖2*s+1‖*‖sourceArchDiagonalSection s g t‖ := by
  rw [sourceArchDiagonalSectionOne, norm_mul, norm_mul, Complex.norm_real]
  have h := (sourceArchDiagonalLog_bounds g t).1
  calc
    _ ≤ ‖2*s+1‖ * 1 * ‖sourceArchDiagonalSection s g t‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem sourceArchDiagonalSectionTwo_bound (s : ℂ) (g : GL (Fin 2) ℂ) (t : ℝ) :
    ‖sourceArchDiagonalSectionTwo s g t‖ ≤
      (‖2*s+1‖^2+‖2*s+1‖)*‖sourceArchDiagonalSection s g t‖ := by
  have h1 := (sourceArchDiagonalLog_bounds g t).1
  have h2 := (sourceArchDiagonalLog_bounds g t).2
  have hcoef : ‖(2*s+1)^2*(sourceArchDiagonalLogOne g t : ℂ)^2 +
      (2*s+1)*(sourceArchDiagonalLogTwo g t : ℂ)‖ ≤ ‖2*s+1‖^2+‖2*s+1‖ := by
    calc
      _ ≤ ‖(2*s+1)^2*(sourceArchDiagonalLogOne g t : ℂ)^2‖ +
          ‖(2*s+1)*(sourceArchDiagonalLogTwo g t : ℂ)‖ := norm_add_le _ _
      _ = ‖2*s+1‖^2 * |sourceArchDiagonalLogOne g t|^2 +
          ‖2*s+1‖ * |sourceArchDiagonalLogTwo g t| := by
        simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖2*s+1‖^2*1^2 + ‖2*s+1‖*1 := by gcongr
      _ = _ := by ring
  rw [sourceArchDiagonalSectionTwo, norm_mul]
  exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)

theorem sourceArchDiagonalSection_deriv_bound (s : ℂ) (g : GL (Fin 2) ℂ) (t : ℝ) :
    ‖deriv (sourceArchDiagonalSection s g) t‖ ≤
      ‖2*s+1‖*‖sourceArchDiagonalSection s g t‖ := by
  rw [sourceArchDiagonalSection_deriv]
  exact sourceArchDiagonalSectionOne_bound s g t

theorem sourceArchDiagonalSection_deriv_two_bound (s : ℂ) (g : GL (Fin 2) ℂ) (t : ℝ) :
    ‖deriv (deriv (sourceArchDiagonalSection s g)) t‖ ≤
      (‖2*s+1‖^2+‖2*s+1‖)*‖sourceArchDiagonalSection s g t‖ := by
  rw [sourceArchDiagonalSection_deriv_two]
  exact sourceArchDiagonalSectionTwo_bound s g t

end
end ArtinMatthews.SourceArchJacquet
