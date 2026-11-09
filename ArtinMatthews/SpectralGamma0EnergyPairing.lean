module

public import ArtinMatthews.SpectralModularGradientChart
public import ArtinMatthews.SpectralGamma0EnergyGraph


set_option backward.privateInPublic true
@[expose] public section

/-! The actual complex mass-plus-gradient form, with exact finite-chart
integrals on genuine smooth periodizations. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace

namespace ArtinMatthews

theorem gamma0Energy_inner (N : ℕ) [NeZero N] (u v : gamma0EnergySpace N) :
    inner ℂ u v = inner ℂ (gamma0EnergyInclusion N u) (gamma0EnergyInclusion N v) +
      inner ℂ (gamma0EnergyGradient N u) (gamma0EnergyGradient N v) :=
  WithLp.prod_inner_apply (u : Gamma0EnergyAmbient N) (v : Gamma0EnergyAmbient N)

theorem gamma0SmoothSeedMass_inner (N : ℕ) [NeZero N] (ψ φ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0SmoothSeedMass N φ) =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        ∫ z in ModularGroup.fd, inner ℂ (gamma0PoincareSeed N ψ.val (q.out⁻¹ • z))
          (gamma0PoincareSeed N φ.val (q.out⁻¹ • z)) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gamma0SeedMass_coeFn N ψ.val q,gamma0SeedMass_coeFn N φ.val q] with z hψ hφ
  change inner ℂ ((gamma0SeedMass N ψ.val q) z) ((gamma0SeedMass N φ.val q) z) = _
  rw [hψ,hφ]

theorem gamma0SeedGradient_inner (N : ℕ) [NeZero N] (ψ φ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SeedGradient N ψ) (gamma0SeedGradient N φ) =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        ∫ z in ModularGroup.fd, inner ℂ
          (h2SectionGradient (gamma0PoincareSeed N ψ.val) (q.out⁻¹ • z))
          (h2SectionGradient (gamma0PoincareSeed N φ.val) (q.out⁻¹ • z)) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [L2.inner_def]
  have hψ := arithmeticPoincareGradientRegionLp_coeFn
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ψ
    (Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹)
  have hφ := arithmeticPoincareGradientRegionLp_coeFn
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) φ
    (Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹)
  apply integral_congr_ae
  filter_upwards [hψ,hφ] with z hψz hφz
  change inner ℂ (arithmeticPoincareGradientRegionLp _ ψ _ z)
    (arithmeticPoincareGradientRegionLp _ φ _ z) = _
  rw [hψz,hφz]
  rfl

theorem gamma0EnergyTest_inner (N : ℕ) [NeZero N] (ψ φ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0EnergyTest N ψ) (gamma0EnergyTest N φ) =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        ((∫ z in ModularGroup.fd, inner ℂ (gamma0PoincareSeed N ψ.val (q.out⁻¹ • z))
          (gamma0PoincareSeed N φ.val (q.out⁻¹ • z))) +
        ∫ z in ModularGroup.fd, inner ℂ
          (h2SectionGradient (gamma0PoincareSeed N ψ.val) (q.out⁻¹ • z))
          (h2SectionGradient (gamma0PoincareSeed N φ.val) (q.out⁻¹ • z))) := by
  rw [gamma0Energy_inner,gamma0EnergyInclusion_test,gamma0EnergyInclusion_test,
    gamma0EnergyGradient_test,gamma0EnergyGradient_test,gamma0SmoothSeedMass_inner,
    gamma0SeedGradient_inner,Finset.sum_add_distrib]

end ArtinMatthews
