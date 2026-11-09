module

public import ArtinMatthews.SpectralGamma0CuspMassRestriction
public import ArtinMatthews.SpectralModularTailIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Low-height cusp strips jointly detect the actual full finite-chart mass. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem modular_fd_im_gt_half {z : UpperHalfPlane} (hz : z ∈ ModularGroup.fd) :
    (1/2 : ℝ) < z.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  by_contra hn
  have hn' := le_of_not_gt hn
  have hm := mul_nonneg z.im_pos.le (sub_nonneg.mpr hn')
  nlinarith

theorem gamma0Seed_modular_mass_le_low_cusps (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    (∫ z in ModularGroup.fd, ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖^2) ≤
      ‖gamma0CuspHeightSeedLp N r (1/2) (by norm_num) ψ‖^2 +
        ‖gamma0CuspHeightSeedLp N (ModularGroup.T*r) (1/2) (by norm_num) ψ‖^2 := by
  let f : UpperHalfPlane → ℝ := fun z => ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖^2
  have hc : Continuous f := ((gamma0PoincareSeed N ψ.val).continuous.comp
    (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹))).norm.pow 2
  have he : (fun z => f (ModularGroup.T⁻¹ • z)) =
      fun z => ‖gamma0CuspSection N ψ (ModularGroup.T*r) z‖^2 := by
    funext z
    simp only [f,gamma0CuspSection,mul_inv_rev,mul_smul]
  have h0 : IntegrableOn f (hyperbolicCuspStrip (N:ℝ) (1/2)) :=
    (gamma0CuspSection_memLp_positive_height N ψ r (1/2) (by norm_num)).integrable_norm_pow
      (by norm_num)
  have h1 : IntegrableOn (fun z => f (ModularGroup.T⁻¹ • z))
      (hyperbolicCuspStrip (N:ℝ) (1/2)) := by
    rw [he]
    exact (gamma0CuspSection_memLp_positive_height N ψ (ModularGroup.T*r)
      (1/2) (by norm_num)).integrable_norm_pow (by norm_num)
  have h := modular_tail_integral_le_two_strips N (1/2) f
    (fun _ => sq_nonneg _) hc.aestronglyMeasurable h0 h1
  have hset : {z : UpperHalfPlane | z ∈ ModularGroup.fd ∧ (1/2:ℝ) < z.im} =
      ModularGroup.fd := by
    ext z
    exact ⟨And.left,fun hz => ⟨hz,modular_fd_im_gt_half hz⟩⟩
  rw [hset,he] at h
  simpa only [gamma0CuspHeightSeedLp,spectral_cusp_toLp_norm_square,f,gamma0CuspSection] using h

theorem gamma0SmoothSeedMass_low_cusps_bound (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) :
    ‖gamma0SmoothSeedMass N ψ‖^2 ≤
      ∑ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        (‖gamma0CuspHeightSeedLp N q.out (1/2) (by norm_num) ψ‖^2 +
          ‖gamma0CuspHeightSeedLp N (ModularGroup.T*q.out) (1/2) (by norm_num) ψ‖^2) := by
  rw [gamma0SmoothSeedMass_norm_sq]
  exact Finset.sum_le_sum (fun q _ => gamma0Seed_modular_mass_le_low_cusps N ψ q.out)

theorem gamma0Mass_low_cusps_bound (N : ℕ) [NeZero N]
    (u : Gamma0RegionL2 N) :
    ‖u‖^2 ≤ ∑ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      (‖gamma0CuspMassRestriction N q.out (1/2) (by norm_num) u‖^2 +
        ‖gamma0CuspMassRestriction N (ModularGroup.T*q.out) (1/2) (by norm_num) u‖^2) := by
  have hc : Continuous (fun u : Gamma0RegionL2 N =>
      ∑ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        (‖gamma0CuspMassRestriction N q.out (1/2) (by norm_num) u‖^2 +
          ‖gamma0CuspMassRestriction N (ModularGroup.T*q.out) (1/2) (by norm_num) u‖^2)) := by
    fun_prop
  apply isClosed_property (gamma0SmoothSeedMass_denseRange N)
    (isClosed_le (continuous_norm.pow 2) hc)
  intro ψ
  simpa only [Pi.pow_apply,gamma0CuspMassRestriction_apply] using
    gamma0SmoothSeedMass_low_cusps_bound N ψ

theorem gamma0Mass_eq_zero_of_low_cusps_eq_zero (N : ℕ) [NeZero N]
    (u : Gamma0RegionL2 N)
    (hu : ∀ r : SL(2,ℤ), gamma0CuspMassRestriction N r (1/2) (by norm_num) u = 0) :
    u = 0 := by
  have h := gamma0Mass_low_cusps_bound N u
  simp only [hu,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,
    add_zero,Finset.sum_const_zero] at h
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _)))

end ArtinMatthews
