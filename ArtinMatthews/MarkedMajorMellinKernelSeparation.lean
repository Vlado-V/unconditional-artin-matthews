module

public import ArtinMatthews.MarkedMajorMellinKernel
public import ArtinMatthews.MarkedMajorFourierSeparationExp


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Complex
noncomputable section

theorem markedMajor_actual_mellin_separation (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {a b R X w w' : ℝ} (ha : 0 < a) (hX : 0 < X)
    (hρ : tsupport ρ ⊆ Set.Icc a b) (hρ' : tsupport ρ' ⊆ Set.Icc a b)
    (hψ : tsupport ψ ⊆ Set.Icc (-R) R) (theta : ℝ)
    (hw : 0 < w) (hw' : 0 < w') (hwρ : ρ w = 1) (hwρ' : ρ' w' = 1) :
    ψ (X*(w-w'))*OAI.Problem337.RealPhase.phase (theta*(X*(w-w'))) =
      (X : ℂ)⁻¹ * ∫ t : ℝ, ∫ s : ℝ,
        markedMajorFourierCoefficient (markedMajorMellinKernel ρ ρ' ψ ha hX hρ hρ' hψ theta) (t/X,s) *
          (Complex.exp (I*(t : ℂ)*(Real.log w : ℂ)) *
            Complex.exp (I*((s-t : ℝ) : ℂ)*(Real.log w' : ℂ))) := by
  rw [← markedMajorMellinKernel_on_source ρ ρ' ψ hX.ne' hw hw' hwρ hwρ' theta]
  exact markedMajor_mellin_separation_exp
    (markedMajorMellinKernel ρ ρ' ψ ha hX hρ hρ' hψ theta) hX hw hw'

theorem markedMajor_actual_mellin_integrable (ρ ρ' ψ : SchwartzMap ℝ ℂ)
    {a b R X w w' : ℝ} (ha : 0 < a) (hX : 0 < X)
    (hρ : tsupport ρ ⊆ Set.Icc a b) (hρ' : tsupport ρ' ⊆ Set.Icc a b)
    (hψ : tsupport ψ ⊆ Set.Icc (-R) R) (theta : ℝ)
    (hw : 0 < w) (hw' : 0 < w') :
    Integrable (fun p : ℝ × ℝ =>
      markedMajorFourierCoefficient (markedMajorMellinKernel ρ ρ' ψ ha hX hρ hρ' hψ theta) (p.1/X,p.2) *
        (Complex.exp (I*(p.1 : ℂ)*(Real.log w : ℂ)) *
          Complex.exp (I*((p.2-p.1 : ℝ) : ℂ)*(Real.log w' : ℂ)))) :=
  markedMajor_mellin_separated_exp_integrable
    (markedMajorMellinKernel ρ ρ' ψ ha hX hρ hρ' hψ theta) hX hw hw'

end
end ArtinMatthews
