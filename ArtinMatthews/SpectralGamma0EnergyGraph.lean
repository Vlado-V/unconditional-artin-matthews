module

public import ArtinMatthews.SpectralPoincareGradientL2
public import ArtinMatthews.SpectralPoincareEnergy
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Function.L2Space


set_option backward.privateInPublic true
@[expose] public section

/-!
The actual Γ₀(N) smooth-core energy completion.  The dimension-independent
closed-graph construction is the one in math-main's CubicThetaGlobalEnergy;
here both coordinates are constructed from genuine H² periodizations and
their actual Fréchet derivatives.  Injectivity of the completed mass map and
compactness of its cuspidal restriction are separate analytic steps.
-/

noncomputable section
open Set MeasureTheory
open scoped CompactlySupported MatrixGroups

namespace ArtinMatthews

abbrev Gamma0GradientL2 (N : ℕ) :=
  PiLp 2 (fun _ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
    Lp (EuclideanSpace ℂ (Fin 2)) 2 (volume.restrict ModularGroup.fd))

def gamma0SeedGradient (N : ℕ) [NeZero N] :
    h2SmoothCompactSeeds →ₗ[ℂ] Gamma0GradientL2 N :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp <|
    LinearMap.pi (fun q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
      arithmeticPoincareGradientRegionLinear
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
        (Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹))

abbrev Gamma0EnergyAmbient (N : ℕ) := WithLp 2 (Gamma0RegionL2 N × Gamma0GradientL2 N)

def gamma0EnergyGraph (N : ℕ) [NeZero N] :
    h2SmoothCompactSeeds →ₗ[ℂ] Gamma0EnergyAmbient N :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (Gamma0RegionL2 N) (Gamma0GradientL2 N)).symm.toLinearMap.comp
    ((gamma0SmoothSeedMass N).prod (gamma0SeedGradient N))

def gamma0EnergySpace (N : ℕ) [NeZero N] : Submodule ℂ (Gamma0EnergyAmbient N) :=
  (gamma0EnergyGraph N).range.topologicalClosure

instance gamma0EnergySpace_complete (N : ℕ) [NeZero N] : CompleteSpace (gamma0EnergySpace N) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def gamma0EnergyTest (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) : gamma0EnergySpace N :=
  ⟨gamma0EnergyGraph N ψ, Submodule.le_topologicalClosure _ ⟨ψ, rfl⟩⟩

def gamma0EnergyInclusion (N : ℕ) [NeZero N] : gamma0EnergySpace N →L[ℂ] Gamma0RegionL2 N :=
  (WithLp.fstL 2 ℂ (Gamma0RegionL2 N) (Gamma0GradientL2 N)).comp (gamma0EnergySpace N).subtypeL

def gamma0EnergyGradient (N : ℕ) [NeZero N] : gamma0EnergySpace N →L[ℂ] Gamma0GradientL2 N :=
  (WithLp.sndL 2 ℂ (Gamma0RegionL2 N) (Gamma0GradientL2 N)).comp (gamma0EnergySpace N).subtypeL

theorem gamma0EnergyInclusion_test (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    gamma0EnergyInclusion N (gamma0EnergyTest N ψ) = gamma0SmoothSeedMass N ψ := rfl

theorem gamma0EnergyGradient_test (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    gamma0EnergyGradient N (gamma0EnergyTest N ψ) = gamma0SeedGradient N ψ := rfl

theorem gamma0EnergyInclusion_bound (N : ℕ) [NeZero N] (u : gamma0EnergySpace N) :
    ‖gamma0EnergyInclusion N u‖ ≤ ‖u‖ :=
  WithLp.norm_fst_le (Gamma0RegionL2 N) (u : Gamma0EnergyAmbient N)

theorem gamma0EnergyInclusion_norm (N : ℕ) [NeZero N] : ‖gamma0EnergyInclusion N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using gamma0EnergyInclusion_bound N u

theorem gamma0Energy_norm_sq (N : ℕ) [NeZero N] (u : gamma0EnergySpace N) :
    ‖u‖ ^ 2 = ‖gamma0EnergyInclusion N u‖ ^ 2 + ‖gamma0EnergyGradient N u‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (u : Gamma0EnergyAmbient N)

/-- Exact actual mass, summed over the finite coset representatives. -/
theorem gamma0SmoothSeedMass_norm_sq (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    ‖gamma0SmoothSeedMass N ψ‖ ^ 2 =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        ∫ z in ModularGroup.fd, ‖gamma0PoincareSeed N ψ.val (q.out⁻¹ • z)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro q _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gamma0SeedMass_coeFn N ψ.val q] with z hz
  rw [real_inner_self_eq_norm_sq]
  change ‖(gamma0SeedMass N ψ.val q) z‖ ^ 2 = _
  rw [hz]

/-- Exact actual derivative energy, with no independent gradient data. -/
theorem gamma0SeedGradient_norm_sq (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    ‖gamma0SeedGradient N ψ‖ ^ 2 =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        ∫ z in ModularGroup.fd, h2SectionEnergy (gamma0PoincareSeed N ψ.val) (q.out⁻¹ • z) := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro q _
  exact arithmeticPoincareGradientRegionLp_norm_sq _ ψ (Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹)

/-- The completed norm agrees on the generating core with the literal mass
plus actual Dirichlet energy of the Γ₀ periodization. -/
theorem gamma0EnergyTest_norm_sq (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    ‖gamma0EnergyTest N ψ‖ ^ 2 =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        ∫ z in ModularGroup.fd, ‖gamma0PoincareSeed N ψ.val (q.out⁻¹ • z)‖ ^ 2 +
          h2SectionEnergy (gamma0PoincareSeed N ψ.val) (q.out⁻¹ • z) := by
  rw [gamma0Energy_norm_sq, gamma0EnergyInclusion_test, gamma0EnergyGradient_test,
    gamma0SmoothSeedMass_norm_sq, gamma0SeedGradient_norm_sq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_add]
  · exact (gamma0PoincareSeed_memLp_modularRegion N ψ.val q.out⁻¹).integrable_norm_pow (by norm_num)
  · exact arithmeticPoincareSeed_energy_integrable _ ψ (Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹)

end ArtinMatthews
