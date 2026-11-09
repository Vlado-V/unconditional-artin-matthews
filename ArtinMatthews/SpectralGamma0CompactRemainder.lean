module

public import ArtinMatthews.SpectralGamma0CompactMass
public import ArtinMatthews.SpectralCutoffMassBound


set_option backward.privateInPublic true
@[expose] public section

/-! Exact global mass remainder and its actual modular-tail bound. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)

theorem gamma0CompactMassMap_seed_remainder_norm_sq (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    ‖gamma0EnergyInclusion N (gamma0EnergyTest N ψ)-
        gamma0CompactMassMap φ ha hab hφ N (gamma0EnergyTest N ψ)‖^2 =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        ∫ z in ModularGroup.fd,
          ‖(1-φ ((q.out⁻¹ • z).re,(q.out⁻¹ • z).im))*gamma0PoincareSeed N ψ.val (q.out⁻¹ • z)‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro q _
  change ‖gamma0EnergyInclusion N (gamma0EnergyTest N ψ) q-
    gamma0CompactMassMap φ ha hab hφ N (gamma0EnergyTest N ψ) q‖^2 = _
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gamma0SeedMass_coeFn N ψ.val q,
    gamma0CompactMassMap_seed_ae φ ha hab hφ N ψ q,
    Lp.coeFn_sub (gamma0EnergyInclusion N (gamma0EnergyTest N ψ) q)
      (gamma0CompactMassMap φ ha hab hφ N (gamma0EnergyTest N ψ) q)] with z hm hc hd
  rw [real_inner_self_eq_norm_sq,hd]
  change ‖(gamma0SeedMass N ψ.val q) z-
    (gamma0CompactMassMap φ ha hab hφ N (gamma0EnergyTest N ψ) q) z‖^2 = _
  rw [hm,hc,sub_mul,one_mul]

theorem gamma0CompactMassMap_seed_remainder_tail_le (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : ℝ)
    (hplateau : ∀ (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane),
      z ∈ ModularGroup.fd → z.im ≤ Y → φ ((q.out⁻¹ • z).re,(q.out⁻¹ • z).im) = 1)
    (hres : ∀ p, ‖1-φ p‖ ≤ 1) :
    ‖gamma0EnergyInclusion N (gamma0EnergyTest N ψ)-
        gamma0CompactMassMap φ ha hab hφ N (gamma0EnergyTest N ψ)‖^2 ≤
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        ∫ z in {z : UpperHalfPlane | z ∈ ModularGroup.fd ∧ Y < z.im},
          ‖gamma0PoincareSeed N ψ.val (q.out⁻¹ • z)‖^2 := by
  rw [gamma0CompactMassMap_seed_remainder_norm_sq]
  apply Finset.sum_le_sum
  intro q _
  have hmem := gamma0PoincareSeed_memLp_modularRegion N ψ.val q.out⁻¹
  have hact : Continuous (fun z : UpperHalfPlane => q.out⁻¹ • z) := by
    change Continuous (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹ • z)
    exact continuous_const_smul _
  have hc : Continuous (fun z : UpperHalfPlane => φ ((q.out⁻¹ • z).re,(q.out⁻¹ • z).im)) :=
    φ.continuous.comp ((UpperHalfPlane.continuous_re.comp hact).prodMk
      (UpperHalfPlane.continuous_im.comp hact))
  have hT : MeasurableSet {z : UpperHalfPlane | Y < z.im} :=
    measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable
  have h := (cutoff_residual_mass_le (volume.restrict ModularGroup.fd)
    (fun z : UpperHalfPlane => gamma0PoincareSeed N ψ.val (q.out⁻¹ • z))
    (fun z => φ ((q.out⁻¹ • z).re,(q.out⁻¹ • z).im)) hT
    (hmem.integrable_norm_pow (by norm_num)) hmem.aestronglyMeasurable hc.aestronglyMeasurable
    (fun z => hres _) (by
      filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
      intro hnot
      exact hplateau q z hz (le_of_not_gt hnot))).2
  rw [Measure.restrict_restrict hT] at h
  simpa only [inter_comm,inter_def,mem_ofPred_eq] using h

end ArtinMatthews
