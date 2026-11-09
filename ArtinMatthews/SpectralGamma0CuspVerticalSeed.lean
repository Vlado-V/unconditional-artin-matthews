module

public import ArtinMatthews.SpectralGamma0CuspHeightRestriction


set_option backward.privateInPublic true
@[expose] public section

/-! The actual height-scaled vertical derivative of every smooth cusp section
belongs to the hyperbolic strip L² space at every positive height. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

def gamma0CuspVerticalField (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) (z : UpperHalfPlane) : ℂ :=
  h2SectionGradient (gamma0CuspSection N ψ r) z 1

theorem gamma0CuspVerticalField_apply (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) (z : UpperHalfPlane) :
    gamma0CuspVerticalField N ψ r z = z.im •
      fderiv ℝ (fun w : ℂ => gamma0CuspSection N ψ r (UpperHalfPlane.ofComplex w))
        (z : ℂ) Complex.I := rfl

theorem gamma0CuspVerticalField_continuous (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) : Continuous (gamma0CuspVerticalField N ψ r) :=
  (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 1).comp
    (h2SectionGradient_continuous _ (gamma0CuspSection_smooth N ψ r))

theorem gamma0CuspVerticalField_sq_le (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (z : UpperHalfPlane) :
    ‖gamma0CuspVerticalField N ψ r z‖ ^ 2 ≤ gamma0CuspEnergyDensity N ψ r z := by
  have hb : ‖gamma0CuspVerticalField N ψ r z‖ ^ 2 ≤
      h2SectionEnergy (gamma0CuspSection N ψ r) z := by
    rw [← h2SectionGradient_norm_sq, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
    exact le_add_of_nonneg_left (sq_nonneg _)
  exact hb.trans (le_add_of_nonneg_left (sq_nonneg _))

theorem gamma0CuspVerticalField_memLp (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    MemLp (gamma0CuspVerticalField N ψ r) 2
      (volume.restrict (hyperbolicCuspStrip (N : ℝ) Y)) := by
  obtain ⟨_, _, hb⟩ := gamma0_cusp_positive_height_energy_bound N r Y hY
  have hc := gamma0CuspVerticalField_continuous N ψ r
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  apply (hb ψ).1.mono' (hc.norm.pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro z
  change ‖‖gamma0CuspVerticalField N ψ r z‖ ^ 2‖ ≤ gamma0CuspEnergyDensity N ψ r z
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact gamma0CuspVerticalField_sq_le N ψ r z

def gamma0CuspVerticalSeedLp (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) : CuspHyperbolicL2 (N : ℝ) Y :=
  (gamma0CuspVerticalField_memLp N ψ r Y hY).toLp (gamma0CuspVerticalField N ψ r)

theorem gamma0CuspVerticalSeedLp_ae (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    gamma0CuspVerticalSeedLp N ψ r Y hY
      =ᵐ[volume.restrict (hyperbolicCuspStrip (N : ℝ) Y)] gamma0CuspVerticalField N ψ r :=
  (gamma0CuspVerticalField_memLp N ψ r Y hY).coeFn_toLp

theorem gamma0CuspVerticalSeedLp_bound (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    ∃ C > 0, ∀ ψ : h2SmoothCompactSeeds,
      ‖gamma0CuspVerticalSeedLp N ψ r Y hY‖ ≤ C * ‖gamma0EnergyTest N ψ‖ := by
  obtain ⟨C, hC, hb⟩ := gamma0_cusp_positive_height_energy_bound N r Y hY
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, fun ψ => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hC.le]
  change ‖(gamma0CuspVerticalField_memLp N ψ r Y hY).toLp
    (gamma0CuspVerticalField N ψ r)‖ ^ 2 ≤ _
  rw [spectral_cusp_toLp_norm_square]
  apply le_trans _ (hb ψ).2
  exact integral_mono
    ((gamma0CuspVerticalField_memLp N ψ r Y hY).integrable_norm_pow (by norm_num))
    (hb ψ).1 (gamma0CuspVerticalField_sq_le N ψ r)

end ArtinMatthews
