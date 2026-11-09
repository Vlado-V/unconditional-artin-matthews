module

public import ArtinMatthews.SpectralCoreLocalizationSmoothEnergy
public import ArtinMatthews.SpectralCompactChartEnergy
public import ArtinMatthews.SpectralGamma0EnergyDense


set_option backward.privateInPublic true
@[expose] public section

/-! Actual fixed compact localizations of the arithmetic smooth energy core. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)

/-- Literal multiplication by a compact smooth cutoff, in invariant-volume L². -/
def gamma0LocalizedSeedLp (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    Lp ℂ 2 (volume : Measure UpperHalfPlane) :=
  spectralHyperbolicRectangleLp ha hab
    (spectralCoreLocalization φ ha hφ (gamma0PoincareSeed N ψ.val)
      (gamma0SmoothSeed_representative_smooth N ψ))
    (spectralCoreLocalization_support φ ha hφ (gamma0PoincareSeed N ψ.val)
      (gamma0SmoothSeed_representative_smooth N ψ))

theorem gamma0LocalizedSeedLp_ae (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    gamma0LocalizedSeedLp φ ha hab hφ N ψ =ᵐ[volume]
      (fun z : UpperHalfPlane => φ (z.re,z.im) * gamma0PoincareSeed N ψ.val z) := by
  filter_upwards [spectralHyperbolicRectangleLp_ae ha hab
    (spectralCoreLocalization φ ha hφ (gamma0PoincareSeed N ψ.val)
      (gamma0SmoothSeed_representative_smooth N ψ))
    (spectralCoreLocalization_support φ ha hφ (gamma0PoincareSeed N ψ.val)
      (gamma0SmoothSeed_representative_smooth N ψ))] with z hz
  change (gamma0LocalizedSeedLp φ ha hab hφ N ψ) z = _ at hz
  rw [hz, spectralCoreLocalization_apply]
  rw [show ((z.re : ℂ)+z.im*Complex.I) = (z : ℂ) from Complex.re_add_im _]
  rw [UpperHalfPlane.ofComplex_apply]

/-- This localization is linear in the actual compact seed. -/
def gamma0LocalizedSeedLinear (N : ℕ) [NeZero N] :
    h2SmoothCompactSeeds →ₗ[ℂ] Lp ℂ 2 (volume : Measure UpperHalfPlane) where
  toFun := gamma0LocalizedSeedLp φ ha hab hφ N
  map_add' ψ ξ := by
    apply Lp.ext
    filter_upwards [gamma0LocalizedSeedLp_ae φ ha hab hφ N (ψ+ξ),
      gamma0LocalizedSeedLp_ae φ ha hab hφ N ψ,
      gamma0LocalizedSeedLp_ae φ ha hab hφ N ξ,
      Lp.coeFn_add (gamma0LocalizedSeedLp φ ha hab hφ N ψ)
        (gamma0LocalizedSeedLp φ ha hab hφ N ξ)] with z hs hψ hξ hadd
    rw [hadd, hs]
    change _ = (gamma0LocalizedSeedLp φ ha hab hφ N ψ) z +
      (gamma0LocalizedSeedLp φ ha hab hφ N ξ) z
    rw [hψ,hξ]
    change φ (z.re,z.im) * arithmeticPoincareSeed _ (ψ.val+ξ.val) z = _
    rw [arithmeticPoincareSeed_add]
    exact mul_add _ _ _
  map_smul' c ψ := by
    apply Lp.ext
    filter_upwards [gamma0LocalizedSeedLp_ae φ ha hab hφ N (c • ψ),
      gamma0LocalizedSeedLp_ae φ ha hab hφ N ψ,
      Lp.coeFn_smul c (gamma0LocalizedSeedLp φ ha hab hφ N ψ)] with z hs hψ hsmul
    simp only [RingHom.id_apply]
    rw [hsmul, hs]
    change _ = c • (gamma0LocalizedSeedLp φ ha hab hφ N ψ) z
    rw [hψ]
    change φ (z.re,z.im) * arithmeticPoincareSeed _ (c • ψ.val) z = _
    rw [arithmeticPoincareSeed_smul]
    change _ * (c * _) = c * (_ * _)
    dsimp only [gamma0PoincareSeed]
    ring

theorem gamma0LocalizedSeedLp_norm_sq (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    ‖gamma0LocalizedSeedLp φ ha hab hφ N ψ‖^2 =
      ∫ z : UpperHalfPlane, ‖φ (z.re,z.im) * gamma0PoincareSeed N ψ.val z‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gamma0LocalizedSeedLp_ae φ ha hab hφ N ψ] with z hz
  rw [real_inner_self_eq_norm_sq, hz]

end ArtinMatthews
