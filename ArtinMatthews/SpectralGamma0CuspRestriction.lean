module

public import ArtinMatthews.SpectralGamma0CuspGraphCore
public import ArtinMatthews.SpectralGamma0LocalizationCompact


set_option backward.privateInPublic true
@[expose] public section

/-! Actual bounded cusp-value restrictions of the global energy completion. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0CuspSection_memLp (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) :
    MemLp (gamma0CuspSection N ψ r) 2 (volume.restrict (hyperbolicCuspStrip (N : ℝ) 1)) := by
  have ht := (gamma0_cusp_strip_energy_bound N ψ r).1
  have hc := spectralSection_continuous _ (gamma0CuspSection_smooth N ψ r)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  apply ht.mono' (hc.norm.pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro z
  change ‖‖gamma0CuspSection N ψ r z‖^2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact le_add_of_nonneg_right (h2SectionEnergy_nonneg _ _)

def gamma0CuspSeedLp (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip (N : ℝ) 1)) :=
  (gamma0CuspSection_memLp N ψ r).toLp (gamma0CuspSection N ψ r)

theorem gamma0CuspSeedLp_ae (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    gamma0CuspSeedLp N ψ r =ᵐ[volume.restrict (hyperbolicCuspStrip (N : ℝ) 1)]
      gamma0CuspSection N ψ r := MemLp.coeFn_toLp _

theorem gamma0CuspSeedLp_norm_sq (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    ‖gamma0CuspSeedLp N ψ r‖^2 =
      ∫ z in hyperbolicCuspStrip (N : ℝ) 1, ‖gamma0CuspSection N ψ r z‖^2 :=
  spectral_cusp_toLp_norm_square _

theorem gamma0CuspSeedLp_norm_sq_bound (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    ‖gamma0CuspSeedLp N ψ r‖^2 ≤ ((N : ℝ)+1)*‖gamma0EnergyTest N ψ‖^2 := by
  rw [gamma0CuspSeedLp_norm_sq]
  apply le_trans _ (gamma0_cusp_strip_energy_bound N ψ r).2
  apply integral_mono ((gamma0CuspSection_memLp N ψ r).integrable_norm_pow (by norm_num))
    (gamma0_cusp_strip_energy_bound N ψ r).1
  intro z
  exact le_add_of_nonneg_right (h2SectionEnergy_nonneg _ _)

theorem gamma0CuspSeedLp_norm_bound (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    ‖gamma0CuspSeedLp N ψ r‖ ≤ Real.sqrt ((N : ℝ)+1)*‖gamma0EnergyTest N ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ)+1)]
  exact gamma0CuspSeedLp_norm_sq_bound N ψ r

def gamma0CuspSeedLinear (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    h2SmoothCompactSeeds →ₗ[ℂ] Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip (N : ℝ) 1)) where
  toFun ψ := gamma0CuspSeedLp N ψ r
  map_add' ψ ξ := by
    apply Lp.ext
    filter_upwards [gamma0CuspSeedLp_ae N (ψ+ξ) r,gamma0CuspSeedLp_ae N ψ r,
      gamma0CuspSeedLp_ae N ξ r,Lp.coeFn_add (gamma0CuspSeedLp N ψ r) (gamma0CuspSeedLp N ξ r)]
      with z hs hψ hξ hadd
    rw [hadd,hs]
    change _ = (gamma0CuspSeedLp N ψ r) z+(gamma0CuspSeedLp N ξ r) z
    rw [hψ,hξ]
    change arithmeticPoincareSeed _ (ψ.val+ξ.val) (r⁻¹ • z) = _
    rw [arithmeticPoincareSeed_add]
    rfl
  map_smul' c ψ := by
    apply Lp.ext
    filter_upwards [gamma0CuspSeedLp_ae N (c • ψ) r,gamma0CuspSeedLp_ae N ψ r,
      Lp.coeFn_smul c (gamma0CuspSeedLp N ψ r)] with z hs hψ hsmul
    simp only [RingHom.id_apply]
    rw [hsmul,hs]
    change _ = c • (gamma0CuspSeedLp N ψ r) z
    rw [hψ]
    change arithmeticPoincareSeed _ (c • ψ.val) (r⁻¹ • z) = _
    rw [arithmeticPoincareSeed_smul]
    rfl

private theorem cusp_seed_bound (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    ∃ C : ℝ, ∀ ψ : h2SmoothCompactSeeds,
      ‖gamma0CuspSeedLinear N r ψ‖ ≤ C * ‖gamma0EnergyTestLinear N ψ‖ :=
  ⟨Real.sqrt ((N : ℝ)+1),fun ψ => gamma0CuspSeedLp_norm_bound N ψ r⟩

private theorem cusp_restriction_exists (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    ∃ A : gamma0EnergySpace N →L[ℂ] Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip (N : ℝ) 1)),
      ∀ ψ, A (gamma0EnergyTestLinear N ψ) = gamma0CuspSeedLinear N r ψ :=
  exists_bounded_extension_of_dense_functions (D := h2SmoothCompactSeeds)
    (gamma0CuspSeedLinear N r) (gamma0EnergyTestLinear N) (gamma0EnergyTest_dense N)
    (gamma0CuspSeedLinear N r).map_add (gamma0CuspSeedLinear N r).map_smul
    (gamma0EnergyTestLinear N).map_add (gamma0EnergyTestLinear N).map_smul
    (cusp_seed_bound N r)

def gamma0CuspEnergyRestriction (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    gamma0EnergySpace N →L[ℂ] Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip (N : ℝ) 1)) :=
  (cusp_restriction_exists N r).choose

theorem gamma0CuspEnergyRestriction_apply (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (ψ : h2SmoothCompactSeeds) :
    gamma0CuspEnergyRestriction N r (gamma0EnergyTest N ψ) = gamma0CuspSeedLp N ψ r :=
  (cusp_restriction_exists N r).choose_spec ψ

theorem gamma0CuspEnergyRestriction_norm_bound (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (u : gamma0EnergySpace N) :
    ‖gamma0CuspEnergyRestriction N r u‖ ≤ Real.sqrt ((N : ℝ)+1)*‖u‖ := by
  apply isClosed_property (gamma0EnergyTest_dense N)
    (isClosed_le (gamma0CuspEnergyRestriction N r).continuous.norm
      (continuous_const.mul continuous_norm))
  intro ψ
  change ‖gamma0CuspEnergyRestriction N r (gamma0EnergyTest N ψ)‖ ≤ _
  rw [gamma0CuspEnergyRestriction_apply]
  exact gamma0CuspSeedLp_norm_bound N ψ r

end ArtinMatthews
