module

public import ArtinMatthews.SpectralKLExponentialRange


set_option backward.privateInPublic true
@[expose] public section

/-! Positive compact smooth density for an actual locally finite measure
supported on the open positive half-line, including restricted Lebesgue. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ArtinMatthews

theorem spectral_positive_measure_memLp_compact (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (g : ℝ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) : MemLp g 2 μ :=
  hg.memLp_of_hasCompactSupport hgc

theorem spectral_positive_cutoff_toLp_tendsto (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (hμ : ∀ᵐ t ∂μ, 0 < t) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    Tendsto (fun n : ℕ => (spectral_positive_measure_memLp_compact μ
      (fun t => (spectralKLPositiveCutoff n t : ℂ)*g t)
      ((spectralKLPositiveCutoff_contDiff n).mul hg).continuous hgc.mul_left).toLp
        (fun t => (spectralKLPositiveCutoff n t : ℂ)*g t)) atTop
      (𝓝 ((spectral_positive_measure_memLp_compact μ g hg.continuous hgc).toLp g)) := by
  have hgm := spectral_positive_measure_memLp_compact μ g hg.continuous hgc
  apply spectral_L2_toLp_tendsto_of_dominated _ _ g hgm (fun t => 4*‖g t‖^2)
    (((memLp_two_iff_integrable_sq_norm hgm.aestronglyMeasurable).mp hgm).const_mul 4)
  · intro n
    filter_upwards with t
    have hm : ‖(spectralKLPositiveCutoff n t : ℂ)*g t-g t‖ ≤ 2*‖g t‖ := by
      calc
        _ ≤ ‖(spectralKLPositiveCutoff n t : ℂ)*g t‖+‖g t‖ := norm_sub_le _ _
        _ ≤ ‖g t‖+‖g t‖ := by
          rw [norm_mul]
          exact add_le_add (mul_le_of_le_one_left (norm_nonneg (g t)) (spectralKLPositiveCutoff_norm_le_one n t)) le_rfl
        _ = _ := by ring
    nlinarith [norm_nonneg ((spectralKLPositiveCutoff n t : ℂ)*g t-g t),norm_nonneg (g t)]
  · filter_upwards [hμ] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [spectralKLPositiveCutoff_eventually_one ht] with n hn
    simp [hn]

theorem spectral_positive_measure_dense_smooth (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (hμ : ∀ᵐ t ∂μ, 0 < t) :
    Dense {u : Lp ℂ 2 μ | ∃ g : ℝ → ℂ, u =ᵐ[μ] g ∧ HasCompactSupport g ∧
      ContDiff ℝ ∞ g ∧ tsupport g ⊆ Ioi (0 : ℝ)} := by
  have hd : Dense {u : Lp ℂ 2 μ | ∃ g : ℝ → ℂ,
      u =ᵐ[μ] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
    Lp.dense_hasCompactSupport_contDiff (by norm_num)
  have hs : {u : Lp ℂ 2 μ | ∃ g : ℝ → ℂ, u =ᵐ[μ] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} ⊆
      closure {u : Lp ℂ 2 μ | ∃ g : ℝ → ℂ, u =ᵐ[μ] g ∧ HasCompactSupport g ∧
        ContDiff ℝ ∞ g ∧ tsupport g ⊆ Ioi (0 : ℝ)} := by
    intro u hu
    obtain ⟨g,hug,hgc,hg⟩ := hu
    have hmeq : (spectral_positive_measure_memLp_compact μ g hg.continuous hgc).toLp g = u := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp _).trans hug.symm
    rw [← hmeq]
    apply mem_closure_of_tendsto (spectral_positive_cutoff_toLp_tendsto μ hμ g hg hgc)
    apply Filter.Eventually.of_forall
    intro n
    obtain ⟨hc,hdiff,hpos⟩ := spectralKLPositiveCutoff_mul_properties g hg hgc n
    exact ⟨_,MemLp.coeFn_toLp _,hc,hdiff,hpos⟩
  intro u
  exact (closure_minimal hs isClosed_closure) (hd u)

def spectralKLPositiveLebesgueMeasure : Measure ℝ := volume.restrict (Ioi 0)

instance spectralKLPositiveLebesgueMeasure_locallyFinite : IsLocallyFiniteMeasure spectralKLPositiveLebesgueMeasure := by
  unfold spectralKLPositiveLebesgueMeasure
  infer_instance

theorem spectralKLPositiveLebesgue_dense_smooth :
    Dense {u : Lp ℂ 2 spectralKLPositiveLebesgueMeasure | ∃ g : ℝ → ℂ,
      u =ᵐ[spectralKLPositiveLebesgueMeasure] g ∧ HasCompactSupport g ∧
        ContDiff ℝ ∞ g ∧ tsupport g ⊆ Ioi (0 : ℝ)} :=
  spectral_positive_measure_dense_smooth _ (ae_restrict_mem measurableSet_Ioi)

end ArtinMatthews
