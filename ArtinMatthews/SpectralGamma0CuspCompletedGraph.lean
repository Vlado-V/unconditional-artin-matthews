module

public import ArtinMatthews.SpectralGamma0CuspDerivative
public import ArtinMatthews.SpectralCuspHyperbolicProjectionRepresentative
public import ArtinMatthews.SpectralCuspGraphRestriction


set_option backward.privateInPublic true
@[expose] public section

/-! The global energy completion maps into the genuine completed cusp graph. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0CuspSeed_residual_eq (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    gamma0CuspSeedLp N ψ r-
      cuspHyperbolicAverageProjection (N : ℝ) 1 zero_lt_one (gamma0CuspSeedLp N ψ r) =
      (spectralCuspSmoothGraphPair (Nat.cast_pos.mpr (NeZero.pos N)) zero_lt_one
        (gamma0CuspSmoothCore N ψ r)).1 := by
  let G := gamma0CuspSmoothCore N ψ r
  have hstrip : MeasurableSet (hyperbolicCuspStrip (N : ℝ) 1) :=
    (measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
      (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  have he : (fun z : UpperHalfPlane => G.toFun (z.re,z.im))
      =ᵐ[volume.restrict (hyperbolicCuspStrip (N : ℝ) 1)] gamma0CuspSection N ψ r := by
    filter_upwards [ae_restrict_mem hstrip] with z hz
    exact spectralSectionSmoothExtension_at_upper zero_lt_one (gamma0CuspSection N ψ r) z hz.2.le
  have hm := (memLp_congr_ae he).mpr (gamma0CuspSection_memLp N ψ r)
  have hlp : hm.toLp (fun z : UpperHalfPlane => G.toFun (z.re,z.im)) = gamma0CuspSeedLp N ψ r := by
    apply Lp.ext
    exact hm.coeFn_toLp.trans (he.trans (gamma0CuspSeedLp_ae N ψ r).symm)
  have hp := cuspHyperbolicMeanZero_ae_representative (N : ℝ) 1
    (Nat.cast_pos.mpr (NeZero.pos N)) zero_lt_one G.toFun G.smooth.continuous hm
  rw [hlp] at hp
  apply Lp.ext
  exact hp.trans (spectralCuspProjectedLp_ae G.smooth
    (Nat.cast_pos.mpr (NeZero.pos N)) zero_lt_one G.energy_integrable).symm

def gamma0CuspEnergyGraph (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    gamma0EnergySpace N →L[ℂ]
      (CuspHyperbolicL2 (N : ℝ) 1 × Lp ℂ 2 (spectralCuspEuclideanMeasure (N : ℝ) 1)) :=
  ((gamma0CuspEnergyRestriction N r)-
    (cuspHyperbolicAverageProjection (N : ℝ) 1 zero_lt_one).comp (gamma0CuspEnergyRestriction N r)).prod
    (gamma0CuspEnergyDerivative N r)

theorem gamma0CuspEnergyGraph_apply (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (ψ : h2SmoothCompactSeeds) :
    gamma0CuspEnergyGraph N r (gamma0EnergyTest N ψ) =
      spectralCuspSmoothGraphPair (Nat.cast_pos.mpr (NeZero.pos N)) zero_lt_one
        (gamma0CuspSmoothCore N ψ r) := by
  apply Prod.ext
  · change gamma0CuspEnergyRestriction N r (gamma0EnergyTest N ψ)-
      cuspHyperbolicAverageProjection (N : ℝ) 1 zero_lt_one
        (gamma0CuspEnergyRestriction N r (gamma0EnergyTest N ψ)) = _
    rw [gamma0CuspEnergyRestriction_apply]
    exact gamma0CuspSeed_residual_eq N ψ r
  · change gamma0CuspEnergyDerivative N r (gamma0EnergyTest N ψ) = _
    rw [gamma0CuspEnergyDerivative_apply]
    rfl

/-- Graph membership follows from the genuine smooth generators and density,
not from an assumed closed-derivative or tail property. -/
theorem gamma0CuspEnergyGraph_mem_completed (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (u : gamma0EnergySpace N) :
    gamma0CuspEnergyGraph N r u ∈
      spectralCuspCompletedGraph (Nat.cast_pos.mpr (NeZero.pos N)) zero_lt_one := by
  apply isClosed_property (gamma0EnergyTest_dense N)
    (isClosed_closure.preimage (gamma0CuspEnergyGraph N r).continuous)
  intro ψ
  change gamma0CuspEnergyGraph N r (gamma0EnergyTest N ψ) ∈ _
  rw [gamma0CuspEnergyGraph_apply]
  exact subset_closure ⟨gamma0CuspSmoothCore N ψ r,rfl⟩

/-- Actual completed energy vectors retain quadratic escape of mass after
subtracting their actual horizontal-average projection. -/
theorem gamma0CuspEnergy_residual_tail_bound (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (u : gamma0EnergySpace N) {Y : ℝ} (hY : 1 ≤ Y) :
    ‖spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY)
      (gamma0CuspEnergyRestriction N r u-
        cuspHyperbolicAverageProjection (N : ℝ) 1 zero_lt_one (gamma0CuspEnergyRestriction N r u))‖^2 ≤
      ((N : ℝ)^2/Y^2) * (((N : ℝ)+1)*‖u‖^2) := by
  have ht := spectralCuspCompletedGraph_tail_sq_norm_le (Nat.cast_pos.mpr (NeZero.pos N))
    zero_lt_one hY (gamma0CuspEnergyGraph_mem_completed N r u)
  change _ ≤ ((N : ℝ)^2/Y^2)*‖gamma0CuspEnergyDerivative N r u‖^2 at ht
  have hd := (sq_le_sq₀ (norm_nonneg (gamma0CuspEnergyDerivative N r u))
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg u))).mpr
      (gamma0CuspEnergyDerivative_norm_bound N r u)
  rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ)+1)] at hd
  exact ht.trans (mul_le_mul_of_nonneg_left hd (div_nonneg (sq_nonneg _) (sq_nonneg _)))

end ArtinMatthews
