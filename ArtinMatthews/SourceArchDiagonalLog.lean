module

public import ArtinMatthews.SourceArchUpperDenominator


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

def sourceArchPositiveDiagonal (t : ℝ) : GL (Fin 2) ℂ :=
  sourceKPDiagonalHom ℂ (Units.mk0 (Real.exp t : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)))

def sourceArchDiagonalWeight (g : GL (Fin 2) ℂ) (t : ℝ) : ℝ :=
  Real.exp (2*t) * ‖g 1 0‖^2

def sourceArchDiagonalDenominator (g : GL (Fin 2) ℂ) (t : ℝ) : ℝ :=
  sourceArchDiagonalWeight g t + ‖g 1 1‖^2

theorem sourceArchBottomNorm_right_diagonal (g : GL (Fin 2) ℂ) (t : ℝ) :
    sourceArchBottomNorm (g * sourceArchPositiveDiagonal t) = sourceArchDiagonalDenominator g t := by
  have h0 : (g * sourceArchPositiveDiagonal t) 1 0 = g 1 0 * (Real.exp t : ℂ) := by
    change ((g : Matrix (Fin 2) (Fin 2) ℂ) * !![(Real.exp t : ℂ), 0; 0, 1]) 1 0 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : (g * sourceArchPositiveDiagonal t) 1 1 = g 1 1 := by
    change ((g : Matrix (Fin 2) (Fin 2) ℂ) * !![(Real.exp t : ℂ), 0; 0, 1]) 1 1 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [sourceArchBottomNorm, h0, h1]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t),
    sourceArchDiagonalDenominator, sourceArchDiagonalWeight]
  rw [show 2*t=t+t by ring, Real.exp_add]
  ring

theorem sourceArchDiagonalDenominator_pos (g : GL (Fin 2) ℂ) (t : ℝ) :
    0 < sourceArchDiagonalDenominator g t := by
  rw [← sourceArchBottomNorm_right_diagonal]
  exact sourceArchBottomNorm_pos _

theorem sourceArchHeight_right_diagonal (g : GL (Fin 2) ℂ) (t : ℝ) :
    sourceArchHeight (g * sourceArchPositiveDiagonal t) =
      ‖(GeneralLinearGroup.det g : ℂ)‖ * Real.exp t / sourceArchDiagonalDenominator g t := by
  have hd : (GeneralLinearGroup.det (sourceArchPositiveDiagonal t) : ℂ) = Real.exp t := by
    simp [sourceArchPositiveDiagonal, sourceKPDiagonalHom,
      GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  rw [sourceArchHeight, map_mul, Units.val_mul, norm_mul, hd,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t), sourceArchBottomNorm_right_diagonal]

theorem sourceArchDiagonalWeight_hasDerivAt (g : GL (Fin 2) ℂ) (t : ℝ) :
    HasDerivAt (sourceArchDiagonalWeight g) (2*sourceArchDiagonalWeight g t) t := by
  change HasDerivAt (fun x => Real.exp (2*x) * ‖g 1 0‖^2)
    (2*(Real.exp (2*t) * ‖g 1 0‖^2)) t
  simpa [mul_assoc, mul_comm, mul_left_comm] using!
    (((hasDerivAt_id t).const_mul 2).exp.mul_const (‖g 1 0‖^2))

theorem sourceArchDiagonalDenominator_hasDerivAt (g : GL (Fin 2) ℂ) (t : ℝ) :
    HasDerivAt (sourceArchDiagonalDenominator g) (2*sourceArchDiagonalWeight g t) t :=
  (sourceArchDiagonalWeight_hasDerivAt g t).add_const _

def sourceArchDiagonalLog (g : GL (Fin 2) ℂ) (t : ℝ) : ℝ :=
  Real.log ‖(GeneralLinearGroup.det g : ℂ)‖ + t - Real.log (sourceArchDiagonalDenominator g t)

def sourceArchDiagonalLogOne (g : GL (Fin 2) ℂ) (t : ℝ) : ℝ :=
  1 - 2*sourceArchDiagonalWeight g t / sourceArchDiagonalDenominator g t

def sourceArchDiagonalLogTwo (g : GL (Fin 2) ℂ) (t : ℝ) : ℝ :=
  4*(sourceArchDiagonalWeight g t / sourceArchDiagonalDenominator g t)^2 -
    4*sourceArchDiagonalWeight g t / sourceArchDiagonalDenominator g t

theorem sourceArchDiagonalLog_eq (g : GL (Fin 2) ℂ) (t : ℝ) :
    sourceArchDiagonalLog g t = Real.log (sourceArchHeight (g*sourceArchPositiveDiagonal t)) := by
  rw [sourceArchHeight_right_diagonal, Real.log_div
    (mul_ne_zero (norm_ne_zero_iff.mpr (GeneralLinearGroup.det g).ne_zero) (Real.exp_ne_zero t))
    (sourceArchDiagonalDenominator_pos g t).ne',
    Real.log_mul (norm_ne_zero_iff.mpr (GeneralLinearGroup.det g).ne_zero) (Real.exp_ne_zero t), Real.log_exp]
  rfl

theorem sourceArchDiagonalLog_hasDerivAt (g : GL (Fin 2) ℂ) (t : ℝ) :
    HasDerivAt (sourceArchDiagonalLog g) (sourceArchDiagonalLogOne g t) t := by
  exact ((hasDerivAt_id t).const_add _).sub
    ((sourceArchDiagonalDenominator_hasDerivAt g t).log (sourceArchDiagonalDenominator_pos g t).ne')

theorem sourceArchDiagonalLogOne_hasDerivAt (g : GL (Fin 2) ℂ) (t : ℝ) :
    HasDerivAt (sourceArchDiagonalLogOne g) (sourceArchDiagonalLogTwo g t) t := by
  have h := (((sourceArchDiagonalWeight_hasDerivAt g t).const_mul 2).div
    (sourceArchDiagonalDenominator_hasDerivAt g t) (sourceArchDiagonalDenominator_pos g t).ne').const_sub 1
  convert h using 1
  · rfl
  · unfold sourceArchDiagonalLogTwo
    field_simp [(sourceArchDiagonalDenominator_pos g t).ne']
    ring

theorem sourceArchDiagonalLog_bounds (g : GL (Fin 2) ℂ) (t : ℝ) :
    |sourceArchDiagonalLogOne g t| ≤ 1 ∧ |sourceArchDiagonalLogTwo g t| ≤ 1 := by
  have hw : 0 ≤ sourceArchDiagonalWeight g t := by unfold sourceArchDiagonalWeight; positivity
  have hq := sourceArchDiagonalDenominator_pos g t
  have hwq : sourceArchDiagonalWeight g t ≤ sourceArchDiagonalDenominator g t :=
    le_add_of_nonneg_right (sq_nonneg _)
  have ha : 0 ≤ sourceArchDiagonalWeight g t / sourceArchDiagonalDenominator g t := div_nonneg hw hq.le
  have hb : sourceArchDiagonalWeight g t / sourceArchDiagonalDenominator g t ≤ 1 := (div_le_one hq).mpr hwq
  constructor
  · unfold sourceArchDiagonalLogOne
    rw [mul_div_assoc]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · unfold sourceArchDiagonalLogTwo
    rw [mul_div_assoc]
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg (2*(sourceArchDiagonalWeight g t / sourceArchDiagonalDenominator g t)-1)],
      by nlinarith [mul_nonneg ha (sub_nonneg.mpr hb)]⟩

end
end ArtinMatthews.SourceArchJacquet
