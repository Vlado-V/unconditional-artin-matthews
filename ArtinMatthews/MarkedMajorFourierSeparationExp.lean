module

public import ArtinMatthews.MarkedMajorFourierSeparationBase
public import ArtinMatthews.MarkedMajorFourierSeparation


set_option backward.privateInPublic true
@[expose] public section

/-! The same exact separation in the exp(i*t*log w) convention used by
the actual normalized endpoint Dirichlet polynomials. -/
namespace ArtinMatthews
open MeasureTheory Complex
noncomputable section

theorem markedMajor_cpow_eq_log_phase {w : ℝ} (hw : 0 < w) (t : ℝ) :
    (w : ℂ)^((t : ℂ)*I) = Complex.exp (I*(t : ℂ)*(Real.log w : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hw.ne'),
    ← Complex.ofReal_log hw.le]
  congr 1
  ring

theorem markedMajor_mellin_separation_exp (g : SchwartzMap (ℝ × ℝ) ℂ)
    {X w w' : ℝ} (hX : 0 < X) (hw : 0 < w) (hw' : 0 < w') :
    g (X*(Real.log w-Real.log w'),Real.log w') =
      (X : ℂ)⁻¹ * ∫ t : ℝ, ∫ s : ℝ,
        markedMajorFourierCoefficient g (t/X,s) *
          (Complex.exp (I*(t : ℂ)*(Real.log w : ℂ)) *
            Complex.exp (I*((s-t : ℝ) : ℂ)*(Real.log w' : ℂ))) := by
  simpa only [markedMajor_cpow_eq_log_phase hw,markedMajor_cpow_eq_log_phase hw'] using
    markedMajor_mellin_separation g hX hw hw'

theorem markedMajor_mellin_separated_exp_integrable (g : SchwartzMap (ℝ × ℝ) ℂ)
    {X w w' : ℝ} (hX : 0 < X) (hw : 0 < w) (hw' : 0 < w') :
    Integrable (fun p : ℝ × ℝ => markedMajorFourierCoefficient g (p.1/X,p.2) *
      (Complex.exp (I*(p.1 : ℂ)*(Real.log w : ℂ)) *
        Complex.exp (I*((p.2-p.1 : ℝ) : ℂ)*(Real.log w' : ℂ)))) := by
  simpa only [markedMajor_cpow_eq_log_phase hw,markedMajor_cpow_eq_log_phase hw'] using
    markedMajor_mellin_separated_integrable g hX hw hw'

end
end ArtinMatthews
