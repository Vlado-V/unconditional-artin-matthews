module

public import ArtinMatthews.CuspAverageProjectionBase
public import ArtinMatthews.SpectralCuspMass


set_option backward.privateInPublic true
@[expose] public section

/-! The actual horizontal average discharges the smooth cusp-tail conditions. -/
noncomputable section
namespace ArtinMatthews

open MeasureTheory Set
open scoped ContDiff

theorem cuspHorizontalMean_continuous {F : ℝ × ℝ → ℂ} (hF : Continuous F) (w : ℝ) :
    Continuous (cuspHorizontalMean w F) := by
  have hc : Continuous (fun y : ℝ => ∫ t in Icc 0 w, F (t,y)) :=
    continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  have hi : Continuous (fun y : ℝ => ∫ t in Ioc 0 w, F (t,y)) := by
    simpa only [integral_Icc_eq_integral_Ioc] using hc
  exact continuous_const.mul hi

theorem cuspMeanZeroRepresentative_continuous {F : ℝ × ℝ → ℂ} (hF : Continuous F) (w : ℝ) :
    Continuous (cuspMeanZeroRepresentative w F) :=
  hF.sub ((cuspHorizontalMean_continuous hF w).comp continuous_snd)

theorem cuspMeanZeroRepresentative_slice_smooth {F : ℝ × ℝ → ℂ} {w y : ℝ}
    (hf : ContDiff ℝ ∞ (fun x => F (x,y))) :
    ContDiff ℝ ∞ (fun x => cuspMeanZeroRepresentative w F (x,y)) := by
  change ContDiff ℝ ∞ (fun x => F (x,y)-cuspHorizontalMean w F y)
  exact hf.sub contDiff_const

theorem cuspMeanZeroRepresentative_deriv (F : ℝ × ℝ → ℂ) (w x y : ℝ) :
    deriv (fun t => cuspMeanZeroRepresentative w F (t,y)) x =
      deriv (fun t => F (t,y)) x := by
  exact deriv_sub_const (cuspHorizontalMean w F y)

theorem cuspMeanZeroRepresentative_energy (F : ℝ × ℝ → ℂ) (w : ℝ) :
    cuspHorizontalEnergy (cuspMeanZeroRepresentative w F) w = cuspHorizontalEnergy F w := by
  funext y
  unfold cuspHorizontalEnergy
  simp only [cuspMeanZeroRepresentative_deriv]

theorem cuspMeanZeroRepresentative_mean_zero {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    {w : ℝ} (hw : 0 < w) (y : ℝ) :
    (∫ x in (0:ℝ)..w, cuspMeanZeroRepresentative w F (x,y)) = 0 := by
  have hi : IntervalIntegrable (fun x : ℝ => F (x,y)) volume 0 w :=
    (hF.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  change (∫ x in (0:ℝ)..w, F (x,y)-cuspHorizontalMean w F y) = 0
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
    intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul, cuspHorizontalMean,
    intervalIntegral.integral_of_le hw.le]
  have hn : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul, sub_self]

/-- The proved cusp-tail inequality for the literal mean-zero representative
of the actual horizontal average. The derivative energy is that of F itself. -/
theorem hyperbolic_cusp_projected_tail_bound {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (hsmooth : ∀ y ∈ Ioi Y, ContDiff ℝ ∞ (fun x => F (x,y)))
    (henergy : IntegrableOn (cuspHorizontalEnergy F w) (Ioi Y)) :
    (∫ z : UpperHalfPlane in hyperbolicCuspStrip w Y,
      ‖cuspMeanZeroRepresentative w F (z.re,z.im)‖^2) ≤
      (w^2/Y^2)*∫ y in Ioi Y, cuspHorizontalEnergy F w y := by
  have hh := hyperbolic_cusp_tail_bound (cuspMeanZeroRepresentative_continuous hF w) hw hY
    (fun y hy => cuspMeanZeroRepresentative_slice_smooth (hsmooth y hy))
    (fun y _ => cuspMeanZeroRepresentative_mean_zero hF hw y)
    (by rwa [cuspMeanZeroRepresentative_energy])
  simpa only [cuspMeanZeroRepresentative_energy] using hh

end ArtinMatthews
