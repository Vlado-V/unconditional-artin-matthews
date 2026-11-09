module

public import ArtinMatthews.SpectralWeberKMellin
public import ArtinMatthews.SpectralWeberKClosedMellin
public import ArtinMatthews.SpectralMellinUniqueness


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine Gaussian Weber evaluation of the doubled-order K integral,
deduced from actual Mellin integrals and uniqueness. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralWeberK_evaluation {ν : ℂ} (hν : |ν.re| < 1/2)
    {p : ℝ} (hp : 0 < p) :
    (∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(x : ℂ)^2)*schlafliBesselK (2*ν) x) =
      ((Real.sqrt Real.pi : ℂ)/(4*Complex.cos ((Real.pi : ℂ)*ν)))*
        ((p : ℂ)^(-(1/2 : ℂ))*(Complex.exp (((1/8 : ℝ)/p : ℝ) : ℂ)*
          schlafliBesselK ν ((1/8 : ℝ)/p))) := by
  let σ : ℝ := (1/2-|ν.re|)/2
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσstrip : σ+|ν.re| < 1/2 := by dsimp [σ]; linarith
  apply spectral_mellin_unique (spectralWeberKTransform ν) (spectralWeberKClosed ν) σ
  · intro t
    exact spectralWeberK_mellin_convergent ν _ (by simpa using hσ) (by simpa using hσstrip)
  · intro t
    exact spectralWeberKClosed_mellin_convergent ν _ (by simpa using hσ) (by simpa using hσstrip)
  · intro t
    rw [spectralWeberK_mellin ν _ (by simpa using hσ) (by simpa using hσstrip),
      spectralWeberKClosed_mellin ν _ (by simpa using hσ) (by simpa using hσstrip)]
  · exact hp
  · exact spectralWeberK_continuousAt hν hp
  · exact spectralWeberKClosed_continuousAt ν hp

end ArtinMatthews
