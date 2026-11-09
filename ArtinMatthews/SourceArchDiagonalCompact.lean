module

public import ArtinMatthews.SourceArchDiagonalDerivative
public import ArtinMatthews.SourceArchLogCompact


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

theorem sourceArchPositiveDiagonal_zero : sourceArchPositiveDiagonal 0 = 1 := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceArchPositiveDiagonal, sourceKPDiagonalHom]

theorem sourceArchDiagonalLog_zero (g : GL (Fin 2) ℂ) :
    sourceArchDiagonalLog g 0 = Real.log (sourceArchHeight g) := by
  rw [sourceArchDiagonalLog_eq, sourceArchPositiveDiagonal_zero, mul_one]

theorem sourceArchDiagonalLog_compact_bound (g : GL (Fin 2) ℂ) {t R : ℝ}
    (ht : |t| ≤ R) : |sourceArchDiagonalLog g t - sourceArchDiagonalLog g 0| ≤ R := by
  have h := sourceArch_log_lipschitz (sourceArchDiagonalLog_hasDerivAt g)
    (fun x => (sourceArchDiagonalLog_bounds g x).1) t 0
  exact h.trans (by simpa only [sub_zero, one_mul] using ht)

theorem sourceArchDiagonalSection_compact_bound (s : ℂ) (g : GL (Fin 2) ℂ)
    {R t B : ℝ} (ht : |t| ≤ R) (hs : |(2*s+1).re| ≤ B) :
    ‖sourceArchDiagonalSection s g t‖ ≤
      Real.exp (B*R) * (sourceArchHeight g)^((2*s+1).re) := by
  have h := sourceArch_log_profile_bound (sourceArchDiagonalLog_compact_bound g ht) hs
  rw [sourceArchDiagonalSection_eq_exp, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simpa only [sourceArchDiagonalLog_zero, Real.rpow_def_of_pos (sourceArchHeight_pos g)] using h

theorem sourceArchDiagonalSection_deriv_compact_bound (s : ℂ) (g : GL (Fin 2) ℂ)
    {R t B : ℝ} (ht : |t| ≤ R) (hs : |(2*s+1).re| ≤ B) :
    ‖deriv (sourceArchDiagonalSection s g) t‖ ≤
      Real.exp (B*R) * ‖2*s+1‖ * (sourceArchHeight g)^((2*s+1).re) := by
  calc
    _ ≤ ‖2*s+1‖*‖sourceArchDiagonalSection s g t‖ := sourceArchDiagonalSection_deriv_bound s g t
    _ ≤ ‖2*s+1‖*(Real.exp (B*R) * (sourceArchHeight g)^((2*s+1).re)) :=
      mul_le_mul_of_nonneg_left (sourceArchDiagonalSection_compact_bound s g ht hs) (norm_nonneg _)
    _ = _ := by ring

theorem sourceArchDiagonalSection_deriv_two_compact_bound (s : ℂ) (g : GL (Fin 2) ℂ)
    {R t B : ℝ} (ht : |t| ≤ R) (hs : |(2*s+1).re| ≤ B) :
    ‖deriv (deriv (sourceArchDiagonalSection s g)) t‖ ≤
      Real.exp (B*R) * (‖2*s+1‖^2+‖2*s+1‖) * (sourceArchHeight g)^((2*s+1).re) := by
  calc
    _ ≤ (‖2*s+1‖^2+‖2*s+1‖)*‖sourceArchDiagonalSection s g t‖ :=
      sourceArchDiagonalSection_deriv_two_bound s g t
    _ ≤ (‖2*s+1‖^2+‖2*s+1‖)*(Real.exp (B*R) * (sourceArchHeight g)^((2*s+1).re)) :=
      mul_le_mul_of_nonneg_left (sourceArchDiagonalSection_compact_bound s g ht hs) (by positivity)
    _ = _ := by ring

end
end ArtinMatthews.SourceArchJacquet
