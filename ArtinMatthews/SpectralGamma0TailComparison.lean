module

public import ArtinMatthews.SpectralGamma0CompactRemainder
public import ArtinMatthews.SpectralGamma0CuspHeightRestriction
public import ArtinMatthews.SpectralModularTailIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Exact comparison of the compact mass remainder with the actual cusp restrictions. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0CuspEnergyRestriction_seed_tail_norm_sq (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (ψ : h2SmoothCompactSeeds) {Y : ℝ} (hY : 1 ≤ Y) :
    ‖spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY)
      (gamma0CuspEnergyRestriction N r (gamma0EnergyTest N ψ))‖^2 =
      ∫ z in hyperbolicCuspStrip (N : ℝ) Y, ‖gamma0CuspSection N ψ r z‖^2 := by
  rw [gamma0CuspEnergyRestriction_apply]
  have hh := spectralLpMeasureRestriction_toLp (spectralCuspHyperbolicMeasure_mono hY)
    (gamma0CuspSection_memLp N ψ r)
    (gamma0CuspSection_memLp_positive_height N ψ r Y (zero_lt_one.trans_le hY))
  change spectralLpMeasureRestriction _ (gamma0CuspSeedLp N ψ r) = _ at hh
  rw [hh,spectral_cusp_toLp_norm_square]

def gamma0CuspTailMass (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y) (u : gamma0EnergySpace N) : ℝ :=
  ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
    (‖spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY)
      (gamma0CuspEnergyRestriction N q.out u)‖^2+
    ‖spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY)
      (gamma0CuspEnergyRestriction N (ModularGroup.T*q.out) u)‖^2)

theorem gamma0CuspTailMass_continuous (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y) :
    Continuous (gamma0CuspTailMass N Y hY) := by
  unfold gamma0CuspTailMass
  apply continuous_finsetSum
  intro q _
  exact (((spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY)).continuous.comp
    (gamma0CuspEnergyRestriction N q.out).continuous).norm.pow 2).add
    (((spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY)).continuous.comp
    (gamma0CuspEnergyRestriction N (ModularGroup.T*q.out)).continuous).norm.pow 2)

theorem gamma0Seed_modular_tail_le (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ z in {z : UpperHalfPlane | z ∈ ModularGroup.fd ∧ Y < z.im},
      ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖^2) ≤
    ‖spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY)
      (gamma0CuspEnergyRestriction N r (gamma0EnergyTest N ψ))‖^2+
    ‖spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY)
      (gamma0CuspEnergyRestriction N (ModularGroup.T*r) (gamma0EnergyTest N ψ))‖^2 := by
  rw [gamma0CuspEnergyRestriction_seed_tail_norm_sq N r ψ hY,
    gamma0CuspEnergyRestriction_seed_tail_norm_sq N (ModularGroup.T*r) ψ hY]
  have he : (fun z : UpperHalfPlane => ‖gamma0CuspSection N ψ r (ModularGroup.T⁻¹ • z)‖^2) =
      (fun z => ‖gamma0CuspSection N ψ (ModularGroup.T*r) z‖^2) := by
    funext z
    simp only [gamma0CuspSection,mul_inv_rev,mul_smul]
  have h0 := (gamma0CuspSection_memLp_positive_height N ψ r Y
    (zero_lt_one.trans_le hY)).integrable_norm_pow (by norm_num)
  have h1 : IntegrableOn (fun z => ‖gamma0CuspSection N ψ r (ModularGroup.T⁻¹ • z)‖^2)
      (hyperbolicCuspStrip (N : ℝ) Y) := by
    rw [he]
    exact (gamma0CuspSection_memLp_positive_height N ψ (ModularGroup.T*r) Y
      (zero_lt_one.trans_le hY)).integrable_norm_pow (by norm_num)
  have hh := modular_tail_integral_le_two_strips N Y
    (fun z => ‖gamma0CuspSection N ψ r z‖^2) (fun _ => sq_nonneg _)
    ((spectralSection_continuous _ (gamma0CuspSection_smooth N ψ r)).norm.pow 2).aestronglyMeasurable h0 h1
  rw [he] at hh
  exact hh

theorem gamma0CompactMassMap_remainder_le_cusp_tails
    (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b) (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y)
    (hplateau : ∀ (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane),
      z ∈ ModularGroup.fd → z.im ≤ Y → φ ((q.out⁻¹ • z).re,(q.out⁻¹ • z).im) = 1)
    (hres : ∀ p, ‖1-φ p‖ ≤ 1) (u : gamma0EnergySpace N) :
    ‖gamma0EnergyInclusion N u-gamma0CompactMassMap φ ha hab hφ N u‖^2 ≤
      gamma0CuspTailMass N Y hY u := by
  apply isClosed_property (gamma0EnergyTest_dense N)
    (isClosed_le (((gamma0EnergyInclusion N).continuous.sub
      (gamma0CompactMassMap φ ha hab hφ N).continuous).norm.pow 2)
      (gamma0CuspTailMass_continuous N Y hY))
  intro ψ
  change ‖gamma0EnergyInclusion N (gamma0EnergyTest N ψ)-
    gamma0CompactMassMap φ ha hab hφ N (gamma0EnergyTest N ψ)‖^2 ≤
      gamma0CuspTailMass N Y hY (gamma0EnergyTest N ψ)
  apply (gamma0CompactMassMap_seed_remainder_tail_le φ ha hab hφ N ψ Y hplateau hres).trans
  unfold gamma0CuspTailMass
  exact Finset.sum_le_sum (fun (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) _ =>
    gamma0Seed_modular_tail_le N ψ q.out hY)

end ArtinMatthews
