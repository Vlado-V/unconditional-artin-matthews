module

public import ArtinMatthews.SpectralGamma0EllipticCompletion
public import ArtinMatthews.SpectralGamma0EllipticMassBound
public import ArtinMatthews.SpectralModularDensity


set_option backward.privateInPublic true
@[expose] public section

/-! Actual localized Euclidean L² representatives for every automorphic mass
vector.  Their restriction to the completed energy domain is exactly the
value component of the native H1Pair, by the actual common dense core. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational

namespace ArtinMatthews

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
  (r : SL(2, ℤ)) (L : ℂ →L[ℝ] ℝ)

def gamma0EllipticMassSeedLinear (N : ℕ) [NeZero N] :
    h2SmoothCompactSeeds →ₗ[ℝ] Lp ℝ 2 (volume : Measure (Fin 2 → ℝ)) :=
  (LinearMap.fst ℝ _ _).comp (gamma0EllipticSeedPairLinear φ ha hφ r L N)

include hab in
theorem gamma0EllipticMassSeed_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds),
      ‖gamma0EllipticMassSeedLinear φ ha hφ r L N ψ‖ ≤ C*‖gamma0SmoothSeedMass N ψ‖ := by
  obtain ⟨C,hC,hbound⟩ := gamma0EllipticLocalizedScalar_mass_bound φ ha hab hφ r L
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,fun N _ ψ => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hC.le]
  change ‖(gamma0EllipticSeedPair φ ha hφ r L N ψ).1‖^2 ≤ _
  unfold gamma0EllipticSeedPair
  rw [spectralEllipticSmoothPair_value_norm_sq]
  exact hbound N ψ

include hab in
private theorem gamma0EllipticMass_linear_bound (N : ℕ) [NeZero N] :
    ∃ C : ℝ, ∀ ψ : h2SmoothCompactSeeds,
      ‖gamma0EllipticMassSeedLinear φ ha hφ r L N ψ‖ ≤
        C*‖(gamma0SmoothSeedMass N).restrictScalars ℝ ψ‖ := by
  obtain ⟨C,_,hC⟩ := gamma0EllipticMassSeed_bound φ ha hab hφ r L
  exact ⟨C,hC N⟩

include hab in
private theorem gamma0EllipticMass_exists (N : ℕ) [NeZero N] :
    ∃ P : Gamma0RegionL2 N →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 2 → ℝ)),
      ∀ ψ, P (gamma0SmoothSeedMass N ψ) = (gamma0EllipticSeedPair φ ha hφ r L N ψ).1 := by
  obtain ⟨C,_,hC⟩ := gamma0EllipticMassSeed_bound φ ha hab hφ r L
  exact exists_real_bounded_extension_of_dense_functions
    (gamma0EllipticMassSeedLinear φ ha hφ r L N) (gamma0SmoothSeedMass N)
    (gamma0SmoothSeedMass_denseRange N)
    (gamma0EllipticMassSeedLinear φ ha hφ r L N).map_add
    (gamma0EllipticMassSeedLinear φ ha hφ r L N).map_smul
    (gamma0SmoothSeedMass N).map_add ((gamma0SmoothSeedMass N).restrictScalars ℝ).map_smul
    ⟨C,hC N⟩

def gamma0EllipticMass (N : ℕ) [NeZero N] :
    Gamma0RegionL2 N →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 2 → ℝ)) :=
  if hab : a ≤ b then (gamma0EllipticMass_exists φ ha hab hφ r L N).choose else 0

include hab in
theorem gamma0EllipticMass_apply (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    gamma0EllipticMass φ ha hφ r L N (gamma0SmoothSeedMass N ψ) =
      (gamma0EllipticSeedPair φ ha hφ r L N ψ).1 := by
  unfold gamma0EllipticMass
  rw [dite_eq_left hab]
  exact (gamma0EllipticMass_exists φ ha hab hφ r L N).choose_spec ψ

include hab in
theorem gamma0EllipticMass_energy (N : ℕ) [NeZero N] (u : gamma0EnergySpace N) :
    gamma0EllipticMass φ ha hφ r L N (gamma0EnergyInclusion N u) =
      (gamma0EllipticPair φ ha hφ r L N u).1 := by
  apply isClosed_property (gamma0EnergyTest_dense N)
    (isClosed_eq ((gamma0EllipticMass φ ha hφ r L N).continuous.comp
      (gamma0EnergyInclusion N).continuous)
      (continuous_fst.comp (gamma0EllipticPair φ ha hφ r L N).continuous))
  intro ψ
  change gamma0EllipticMass φ ha hφ r L N (gamma0EnergyInclusion N (gamma0EnergyTest N ψ)) =
    (gamma0EllipticPair φ ha hφ r L N (gamma0EnergyTest N ψ)).1
  rw [gamma0EnergyInclusion_test,gamma0EllipticMass_apply φ ha hab hφ r L N,
    gamma0EllipticPair_apply]

include hab in
theorem gamma0EllipticMass_seed_ae (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    gamma0EllipticMass φ ha hφ r L N (gamma0SmoothSeedMass N ψ) =ᵐ[volume]
      fun x : Fin 2 → ℝ => L (φ (spectralEllipticCoordinates x)*
        gamma0CuspSection N ψ r (UpperHalfPlane.ofComplex
          (Complex.equivRealProdCLM.symm (spectralEllipticCoordinates x)))) := by
  rw [gamma0EllipticMass_apply φ ha hab hφ r L N]
  rw [← gamma0EllipticPair_apply]
  exact gamma0EllipticPair_seed_value_ae φ ha hφ r L N ψ

end ArtinMatthews
