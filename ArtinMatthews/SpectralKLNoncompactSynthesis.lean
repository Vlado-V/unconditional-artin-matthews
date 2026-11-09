module

public import ArtinMatthews.SpectralKLCoshDifferenceRange
public import ArtinMatthews.SpectralKLCompactInverse


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped Topology ContDiff
noncomputable section

def spectralKLDataCutoff (F : ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (spectralKLRangeCutoff n t : ℂ) * F t

theorem spectralKLDataCutoff_test (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ))) (n : ℕ) :
    spectralKLDataCutoff F n ∈ spectralKLTestSubmodule := by
  have hp : tsupport (spectralKLDataCutoff F n) ⊆ Ioi (0 : ℝ) :=
    tsupport_mul_subset_left.trans (spectralKLRangeCutoff_tsupport n)
  have hc : HasCompactSupport (spectralKLDataCutoff F n) :=
    (spectralKLRangeCutoff_hasCompactSupport n).mul_right
  have hd : ContDiffOn ℝ ∞ (spectralKLDataCutoff F n) (Ioi (0 : ℝ)) :=
    (spectralKLRangeCutoff_contDiff n).contDiffOn.mul hF
  refine ⟨?_, hc, hp⟩
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : 0 < t
  · exact hd.contDiffAt (isOpen_Ioi.mem_nhds ht)
  · have hn : t ∉ tsupport (spectralKLDataCutoff F n) := fun h => ht (hp h)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)

def spectralKLDataCutoffTest (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ))) (n : ℕ) :
    spectralKLTestSubmodule := ⟨spectralKLDataCutoff F n, spectralKLDataCutoff_test F hF n⟩

theorem spectralKLDataCutoffTest_tendsto (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ))) (hLp : MemLp F 2 spectralKLSpectralMeasure) :
    Tendsto (fun n => spectralKLTestToLp (spectralKLDataCutoffTest F hF n)) atTop (𝓝 (hLp.toLp F)) := by
  have hmem (n : ℕ) : MemLp (spectralKLDataCutoff F n) 2 spectralKLSpectralMeasure :=
    spectralKLSpectralMeasure_memLp_compact _ (spectralKLDataCutoff_test F hF n).1.continuous
      (spectralKLDataCutoff_test F hF n).2.1
  change Tendsto (fun n => (hmem n).toLp (spectralKLDataCutoff F n)) atTop _
  apply spectral_L2_toLp_tendsto_of_dominated _ hmem _ hLp
    (fun t => 4 * ‖F t‖ ^ 2)
    (((memLp_two_iff_integrable_sq_norm hLp.aestronglyMeasurable).mp hLp).const_mul 4)
  · intro n
    filter_upwards with t
    have hη : ‖(spectralKLRangeCutoff n t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (spectralKLRangeCutoff_bounds n t).1]
      exact (spectralKLRangeCutoff_bounds n t).2
    have hb : ‖spectralKLDataCutoff F n t - F t‖ ≤ 2 * ‖F t‖ := by
      calc
        _ ≤ ‖spectralKLDataCutoff F n t‖ + ‖F t‖ := norm_sub_le _ _
        _ ≤ ‖F t‖ + ‖F t‖ := by
          unfold spectralKLDataCutoff
          rw [norm_mul]
          exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hη) le_rfl
        _ = _ := by ring
    nlinarith [norm_nonneg (spectralKLDataCutoff F n t - F t), norm_nonneg (F t)]
  · filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [spectralKLRangeCutoff_eventually_one ht] with n hn
    simp [spectralKLDataCutoff, hn]

theorem spectralKLDataCutoff_synthesis_tendsto (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ))) {x : ℝ} (hx : 0 < x)
    (hI : IntegrableOn (fun t : ℝ => schlafliBesselK ((t : ℂ) * Complex.I) x * F t *
      (spectralKLPlancherelWeight t : ℂ)) (Ioi (0 : ℝ))) :
    Tendsto (fun n => spectralKLWeightedSynthesis (spectralKLDataCutoff F n) x) atTop
      (𝓝 (spectralKLWeightedSynthesis F x)) := by
  unfold spectralKLWeightedSynthesis
  apply tendsto_integral_of_dominated_convergence
    (fun t : ℝ => ‖schlafliBesselK ((t : ℂ) * Complex.I) x * F t *
      (spectralKLPlancherelWeight t : ℂ)‖)
  · intro n
    exact (spectralKLWeightedSynthesis_integrand_integrable _
      (spectralKLDataCutoff_test F hF n).1.continuous
      (spectralKLDataCutoff_test F hF n).2.1 hx).aestronglyMeasurable
  · exact hI.norm
  · intro n
    filter_upwards with t
    have hη : ‖(spectralKLRangeCutoff n t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (spectralKLRangeCutoff_bounds n t).1]
      exact (spectralKLRangeCutoff_bounds n t).2
    rw [show schlafliBesselK ((t : ℂ) * Complex.I) x * spectralKLDataCutoff F n t *
        (spectralKLPlancherelWeight t : ℂ) = (spectralKLRangeCutoff n t : ℂ) *
        (schlafliBesselK ((t : ℂ) * Complex.I) x * F t * (spectralKLPlancherelWeight t : ℂ)) by
      unfold spectralKLDataCutoff; ring, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hη
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [spectralKLRangeCutoff_eventually_one ht] with n hn
    simp [spectralKLDataCutoff, hn]

theorem spectralKLCompletedSynthesis_integral_ae (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ))) (hLp : MemLp F 2 spectralKLSpectralMeasure)
    (hI : ∀ x : ℝ, 0 < x → IntegrableOn
      (fun t : ℝ => schlafliBesselK ((t : ℂ) * Complex.I) x * F t * (spectralKLPlancherelWeight t : ℂ))
      (Ioi (0 : ℝ))) :
    spectralKLCompletedSynthesis (hLp.toLp F) =ᵐ[spectralKLPhysicalMeasure]
      spectralKLWeightedSynthesis F := by
  have hlim : Tendsto (fun n => spectralKLTestSynthesis (spectralKLDataCutoffTest F hF n)) atTop
      (𝓝 (spectralKLCompletedSynthesis (hLp.toLp F))) := by
    have h := spectralKLCompletedSynthesis.continuous.continuousAt.tendsto.comp
      (spectralKLDataCutoffTest_tendsto F hF hLp)
    simpa only [Function.comp_def, spectralKLCompletedSynthesis_test] using h
  apply spectral_Lp_limit_ae_of_pointwise _ _ hlim
    (fun n => spectralKLWeightedSynthesis (spectralKLDataCutoff F n))
    (fun n => spectralKLTestSynthesis_coe (spectralKLDataCutoffTest F hF n))
  filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
  exact spectralKLDataCutoff_synthesis_tendsto F hF hx (hI x hx)

end
end ArtinMatthews
