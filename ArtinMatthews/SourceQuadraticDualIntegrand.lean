module

public import ArtinMatthews.SourceQuadraticDualContourIntegral
public import ArtinMatthews.QuadraticHeckeCoprimeDualSquareContour


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Complex MeasureTheory Set VaryingKummerAnalytic
open OAI.SevenEighths.ProbePhysical
open scoped NumberField Classical ContDiff BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]

theorem quadraticDualContourIntegrand_integrable (m : Ideal (𝓞 F))
    (A : ℝ) (r : ℕ) (w : ℝ → ℂ) (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0)
    (hs : ContDiff ℝ ∞ w) {σ X : ℝ} (hσ : 0 < σ) (hσtop : σ ≤ 5 / 4)
    (hσone : σ ≠ 1) (hX : 0 < X) :
    Integrable (fun t : ℝ => quadraticDualContourKernel F A r w σ t *
      (X : ℂ) ^ quadraticPoissonLine σ t * quadraticSmallEuler F m (quadraticPoissonLine σ t)) := by
  apply (quadraticPoissonLine_cpow_integrable _
    (quadraticDualContourKernel_continuous F A r w hc hp hs hσ hσone)
    (quadraticDualContourKernel_integrable F A r w hc hp hs hσ hσtop hσone) σ hX).mul_bdd
  · exact ((quadraticSmallEuler_continuous F m).comp (by
      unfold quadraticPoissonLine
      fun_prop)).aestronglyMeasurable
  · exact ae_of_all _ (fun t => quadraticSmallEuler_norm_le F m
      (by rw [quadraticPoissonLine_re]; exact hσ.le))

theorem quadraticDualContourRemainder_line_independent
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {σ τ X : ℝ} (hσ : 0 < σ) (hσ₁ : σ < 1) (hτ : 0 < τ) (hτ₁ : τ < 1) (hX : 0 < X) :
    quadraticHeckeCoprimeContourRemainder F m
      (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w)) σ X =
    quadraticHeckeCoprimeContourRemainder F m
      (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w)) τ X := by
  have h₁ := quadraticHeckeCoprimeDualSquareNormContour_shift F m hm A r w hc hp hs hσ hσ₁ hX
  have h₂ := quadraticHeckeCoprimeDualSquareNormContour_shift F m hm A r w hc hp hs hτ hτ₁ hX
  exact add_right_cancel (h₁.symm.trans h₂)

end
end ArtinMatthews
