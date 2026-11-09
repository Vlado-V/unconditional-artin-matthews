module

public import ArtinMatthews.SpectralGamma0EllipticEigenPlane
public import ArtinMatthews.SpectralGamma0LocalFourierBessel


set_option backward.privateInPublic true
@[expose] public section

/-! The native cuspidal spectral basis has the actual K-Bessel Fourier
coefficients. Smoothness, local periodicity, the eigen-equation, and both
energy hypotheses are all discharged by the actual completed constructions. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0FullCuspidalSpectralBasis_fourier_bessel_ae
    (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    ∃ a : ℂ, gamma0CuspFourierCoefficient N r Y hY n
        (gamma0FullCuspidalSpectralBasis N i).val =ᵐ[volume.restrict (Ioi Y)]
      fun y => a * ((Real.sqrt y : ℂ) * OAI.CubicEisenstein.schlafliBesselK
        (Complex.sqrt (1 / 4 - (gamma0AllHeightGradientSpectralValue N i : ℂ)))
        (|cuspFourierFrequency (N : ℝ) n| * y)) := by
  obtain ⟨u, hu, hrep, hp, hEq⟩ :=
    gamma0FullCuspidalSpectralBasis_plane_smooth_periodic_classical N i r Y hY
  have hmass : gamma0EnergyInclusion N (gamma0AllHeightSpectralEnergy N i).val =
      (gamma0FullCuspidalSpectralBasis N i).val :=
    (gamma0AllHeightSpectralEnergy_mass_ambient N i).trans
      (gamma0FullCuspidalSpectralBasis_coe N i).symm
  have h := gamma0CuspLocalFourier_bessel_ae N r Y hY n hn
    (gamma0AllHeightSpectralEnergy N i).val u hu (by rw [hmass]; exact hrep)
    (fun x t hx hxt ht => hp (x, t) ⟨hx, hxt, ht⟩)
    (gamma0AllHeightGradientSpectralValue N i) hEq
  simpa only [hmass] using h

theorem gamma0FullCuspidalSpectralBasis_twoCell_fourier_bessel_ae
    (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    ∃ a : ℂ, gamma0CuspTwoCellFourierCoefficient N r Y hY n
        (gamma0FullCuspidalSpectralBasis N i).val =ᵐ[volume.restrict (Ioi Y)]
      fun y => a * ((Real.sqrt y : ℂ) * OAI.CubicEisenstein.schlafliBesselK
        (Complex.sqrt (1 / 4 - (gamma0AllHeightGradientSpectralValue N i : ℂ)))
        (|cuspFourierFrequency (N : ℝ) n| * y)) := by
  obtain ⟨a, ha⟩ := gamma0FullCuspidalSpectralBasis_fourier_bessel_ae N i r Y hY n hn
  refine ⟨a, ?_⟩
  have htwo : gamma0CuspTwoCellFourierCoefficient N r Y hY n
      (gamma0FullCuspidalSpectralBasis N i).val =ᵐ[volume.restrict (Ioi Y)]
      gamma0CuspFourierCoefficient N r Y hY n
        (gamma0FullCuspidalSpectralBasis N i).val :=
    (spectralHorizontal_cuspVertical_ae_iff hY).mp
    (gamma0CuspTwoCellFourierCoefficient_ae N r Y hY n
      (gamma0FullCuspidalSpectralBasis N i).val)
  exact Filter.EventuallyEq.trans htwo ha

end ArtinMatthews
