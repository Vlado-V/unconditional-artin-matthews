module

public import ArtinMatthews.SpectralJOddSynthesisGaussian
public import ArtinMatthews.SpectralJGaussianLegendreCoefficients
public import ArtinMatthews.SpectralBesselLegendreGaussian
public import ArtinMatthews.ShiftedLegendreBasis


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open MeasureTheory Set
noncomputable section

/-- The Gaussian pairing of the odd synthesis is the unit-interval part of the
order-zero Bessel transform, with its exact Legendre normalization. -/
theorem spectralJOddSynthesis_gaussian_calibrated (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (p : ℝ) (hp : 1 / 4 < p) :
    (∫ x in Ioi (0 : ℝ), (Real.exp (-(p * x ^ 2)) : ℂ) * spectralJOddSynthesis f x) =
      ((1 / (4 * p) : ℝ) : ℂ) * ∫ u in (0 : ℝ)..1,
        (Real.exp (-u / (4 * p)) : ℂ) * spectralJGaussianTransform f (2 * u) := by
  let F : ℝ → ℂ := fun u => spectralJGaussianTransform f (2 * u)
  let G : ℝ → ℂ := fun u => (Real.exp (-u / (4 * p)) : ℂ)
  let C : ℂ := ((1 / (4 * p) : ℝ) : ℂ)
  have hfi : IntegrableOn f (Ioi (0 : ℝ)) :=
    (hf.integrable_of_hasCompactSupport hc).integrableOn
  have hF : Continuous F :=
    (spectralJGaussianTransform_continuous f hf hfi).comp (continuous_const.mul continuous_id)
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hcoef (n : ℕ) :
      (∫ u in (0 : ℝ)..1, (shiftedLegendreValue n u : ℂ) * F u) =
        2 * spectralJDiscreteCoefficient f (2 * n + 1) :=
    spectralJGaussianTransform_legendre_coefficient f hf hfi n
  have hpair := (shiftedLegendreInterval_bilinear_hasSum hG.continuousOn hF.continuousOn).mul_left C
  have hseries := spectralJOddSynthesis_gaussian_hasSum f hf hc hs p hp
  refine hseries.unique (hpair.congr_fun (fun n => ?_))
  rw [(spectral_besselJ_odd_gaussian n p (by linarith)).2, hcoef]
  simp only [spectralLegendreValue, shiftedLegendreValue, G, C]
  push_cast
  ring

end
end ArtinMatthews
