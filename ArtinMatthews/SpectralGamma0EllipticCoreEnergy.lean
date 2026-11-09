module

public import ArtinMatthews.SpectralGamma0EllipticEnergy
public import ArtinMatthews.SpectralGamma0CuspPositiveHeightCompact
public import ArtinMatthews.SpectralGamma0EnergyDense


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform genuine Euclidean H¹ energy bounds for compactly localized
real and imaginary projections of the actual arithmetic smooth core. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff MatrixGroups

namespace ArtinMatthews

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b) (r : SL(2, ℤ))

def gamma0EllipticLocalizedSchwartz (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    SchwartzMap (ℝ × ℝ) ℂ :=
  spectralCoreLocalization φ ha hφ (gamma0CuspSection N ψ r)
    (gamma0CuspSection_smooth N ψ r)

theorem gamma0EllipticLocalizedSchwartz_apply (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (p : ℝ × ℝ) :
    gamma0EllipticLocalizedSchwartz φ ha hφ r N ψ p =
      φ p * gamma0CuspSection N ψ r (UpperHalfPlane.ofComplex (p.1+p.2*Complex.I)) :=
  spectralCoreLocalization_apply _ _ _ _ _ _

theorem gamma0EllipticLocalizedSchwartz_compact (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) :
    HasCompactSupport (gamma0EllipticLocalizedSchwartz φ ha hφ r N ψ) :=
  (spectralPlaneRectangle_compact A a b).of_isClosed_subset (isClosed_tsupport _)
    (spectralCoreLocalization_support φ ha hφ _ _)

theorem gamma0EllipticLocalizedSchwartz_add (N : ℕ) [NeZero N]
    (ψ ξ : h2SmoothCompactSeeds) :
    gamma0EllipticLocalizedSchwartz φ ha hφ r N (ψ+ξ) =
      gamma0EllipticLocalizedSchwartz φ ha hφ r N ψ +
      gamma0EllipticLocalizedSchwartz φ ha hφ r N ξ := by
  ext p
  simp only [add_apply,gamma0EllipticLocalizedSchwartz_apply]
  change φ p * arithmeticPoincareSeed _ (ψ.val+ξ.val) _ = _
  rw [arithmeticPoincareSeed_add]
  exact mul_add _ _ _

theorem gamma0EllipticLocalizedSchwartz_smul (N : ℕ) [NeZero N] (c : ℝ)
    (ψ : h2SmoothCompactSeeds) :
    gamma0EllipticLocalizedSchwartz φ ha hφ r N (c • ψ) =
      c • gamma0EllipticLocalizedSchwartz φ ha hφ r N ψ := by
  ext p
  simp only [smul_apply,gamma0EllipticLocalizedSchwartz_apply]
  change φ p * arithmeticPoincareSeed _ ((c : ℂ) • ψ.val) _ = _
  rw [arithmeticPoincareSeed_smul]
  change _ * ((c : ℂ)*_) = (c : ℂ)*(_*_)
  dsimp only [gamma0CuspSection,gamma0PoincareSeed]
  ring

theorem gamma0EllipticLocalizedScalar_energy_bound (L : ℂ →L[ℝ] ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds),
      spectralEllipticScalarEnergy L (gamma0EllipticLocalizedSchwartz φ ha hφ r N ψ) ≤
        C * ‖gamma0EnergyTest N ψ‖^2 := by
  obtain ⟨C₁,hC₁,hbound⟩ := spectralCoreLocalization_energy_bound_smooth φ ha hφ
  obtain ⟨C₂,hC₂,hchart⟩ := compact_chart_gamma0_cusp_energy_bound r
    (spectralCoreChart_compact A a b ha)
  refine ⟨(‖L‖^2+1)*C₁*C₂,by positivity,fun N _ ψ => ?_⟩
  have hb := hbound (gamma0CuspSection N ψ r) (gamma0CuspSection_smooth N ψ r)
  have he := spectralEllipticScalarEnergy_le L (gamma0EllipticLocalizedSchwartz φ ha hφ r N ψ)
    (gamma0EllipticLocalizedSchwartz_compact φ ha hφ r N ψ)
  have hc := hchart N ψ
  calc
    _ ≤ ‖L‖^2 * (C₁*(∫ z : UpperHalfPlane in
        {z | (z.re,z.im) ∈ spectralPlaneRectangle A a b},
        ‖gamma0CuspSection N ψ r z‖^2+h2SectionEnergy (gamma0CuspSection N ψ r) z)) :=
      he.trans (mul_le_mul_of_nonneg_left hb (sq_nonneg _))
    _ ≤ ‖L‖^2 * (C₁*(C₂*‖gamma0EnergyTest N ψ‖^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hC₁.le) (sq_nonneg _)
    _ ≤ _ := by nlinarith [sq_nonneg ‖gamma0EnergyTest N ψ‖,
      mul_nonneg hC₁.le hC₂.le]

end ArtinMatthews
