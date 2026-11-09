module

public import ArtinMatthews.SpectralBoundedSeedMultiplier


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact-seed mass map is bounded when the fixed seed is
multiplied by arbitrary bounded continuous functions. Constants retain the
fixed level and seed through the actual absolute-seed mass norm. -/
noncomputable section
open Set MeasureTheory Filter
open scoped CompactlySupported MatrixGroups BoundedContinuousFunction
namespace ArtinMatthews

def gamma0BoundedSeedMassLinear (N : ℕ) [NeZero N] (ψ : C_c(UpperHalfPlane,ℂ)) :
    (UpperHalfPlane →ᵇ ℂ) →ₗ[ℂ] Gamma0RegionL2 N :=
  (gamma0SeedMass N).comp (spectralBoundedSeedProductLinear ψ)

theorem gamma0BoundedSeedMass_chart_bound (N : ℕ) [NeZero N] (ψ : C_c(UpperHalfPlane,ℂ))
    (b : UpperHalfPlane →ᵇ ℂ) (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    ‖gamma0BoundedSeedMassLinear N ψ b q‖ ≤ ‖b‖*‖gamma0SeedMass N (spectralAbsoluteSeed ψ) q‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [gamma0SeedMass_coeFn N (spectralBoundedSeedProduct ψ b) q,
    gamma0SeedMass_coeFn N (spectralAbsoluteSeed ψ) q] with z hz hρ
  change ‖gamma0SeedMass N (spectralBoundedSeedProduct ψ b) q z‖ ≤ _
  rw [hz,hρ]
  exact arithmeticPoincare_bounded_seed_norm
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ψ b (q.out⁻¹ • z)

theorem gamma0BoundedSeedMass_norm_bound (N : ℕ) [NeZero N] (ψ : C_c(UpperHalfPlane,ℂ))
    (b : UpperHalfPlane →ᵇ ℂ) :
    ‖gamma0BoundedSeedMassLinear N ψ b‖ ≤ ‖b‖*‖gamma0SeedMass N (spectralAbsoluteSeed ψ)‖ := by
  have hq (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) := gamma0BoundedSeedMass_chart_bound N ψ b q
  have he : ‖gamma0BoundedSeedMassLinear N ψ b‖^2 ≤
      (‖b‖*‖gamma0SeedMass N (spectralAbsoluteSeed ψ)‖)^2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q _
    have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (hq q)
    simpa only [mul_pow] using h
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp he

def gamma0BoundedSeedMass (N : ℕ) [NeZero N] (ψ : C_c(UpperHalfPlane,ℂ)) :
    (UpperHalfPlane →ᵇ ℂ) →L[ℂ] Gamma0RegionL2 N :=
  (gamma0BoundedSeedMassLinear N ψ).mkContinuous ‖gamma0SeedMass N (spectralAbsoluteSeed ψ)‖
    (fun b => by simpa only [mul_comm] using gamma0BoundedSeedMass_norm_bound N ψ b)

theorem gamma0BoundedSeedMass_norm (N : ℕ) [NeZero N] (ψ : C_c(UpperHalfPlane,ℂ)) :
    ‖gamma0BoundedSeedMass N ψ‖ ≤ ‖gamma0SeedMass N (spectralAbsoluteSeed ψ)‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _)
    (fun b => by simpa only [mul_comm] using gamma0BoundedSeedMass_norm_bound N ψ b)

theorem gamma0BoundedSeedMass_ae (N : ℕ) [NeZero N] (ψ : C_c(UpperHalfPlane,ℂ))
    (b : UpperHalfPlane →ᵇ ℂ) (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (gamma0BoundedSeedMass N ψ b q : UpperHalfPlane → ℂ)=ᵐ[volume.restrict ModularGroup.fd]
      (fun z => gamma0PoincareSeed N (spectralBoundedSeedProduct ψ b) (q.out⁻¹ • z)) :=
  gamma0SeedMass_coeFn N _ q

end ArtinMatthews
