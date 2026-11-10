module

public import ArtinMatthews.SourceHyperbolicMeasureGreen
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators
noncomputable section

def gradientEnergy (f : EuclideanSpatial → ℂ) (p : EuclideanSpatial) : ℝ :=
  (p 2)^2 * ∑ j : Fin 3, ‖coordinatePartial f j p‖^2

theorem gradientEnergy_nonneg (f : EuclideanSpatial → ℂ) (p : EuclideanSpatial) :
    0 ≤ gradientEnergy f p := by
  unfold gradientEnergy
  positivity

theorem gradientPair_self (f : EuclideanSpatial → ℂ) (p : EuclideanSpatial) :
    gradientPair f f p = (gradientEnergy f p : ℂ) := by
  unfold gradientPair gradientEnergy
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Complex.star_def, Complex.ofReal_pow] using! RCLike.conj_mul (coordinatePartial f j p)

theorem gradientEnergy_integrable {φ : EuclideanSpatial → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ euclideanUpperHalf) :
    Integrable (gradientEnergy φ) hyperbolicEuclideanVolume := by
  have h := (gradientPair_integrable (fun _ _ => hφ.contDiffAt) hφ hc hsupp).re
  change Integrable (fun p => (gradientPair φ φ p).re) _ at h
  simpa only [gradientPair_self, Complex.ofReal_re] using! h

theorem green_energy {φ : EuclideanSpatial → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ euclideanUpperHalf) :
    (∫ p, star (φ p) * positiveEuclideanLaplacian φ p ∂hyperbolicEuclideanVolume) =
      (∫ p, gradientEnergy φ p ∂hyperbolicEuclideanVolume : ℝ) := by
  calc
    _ = ∫ p, gradientPair φ φ p ∂hyperbolicEuclideanVolume :=
      (green_hyperbolic (fun _ _ => hφ.contDiffAt) hφ hc hsupp).symm
    _ = _ := by
      simp only [gradientPair_self]
      exact integral_complex_ofReal

theorem green_energy_nonneg {φ : EuclideanSpatial → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ euclideanUpperHalf) :
    0 ≤ (∫ p, star (φ p) * positiveEuclideanLaplacian φ p ∂hyperbolicEuclideanVolume).re := by
  rw [green_energy hφ hc hsupp, Complex.ofReal_re]
  exact integral_nonneg (gradientEnergy_nonneg φ)

end
end ArtinMatthews.SourceHyperbolicGreen
