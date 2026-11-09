module

public import ArtinMatthews.SpectralKLWeightedMeasures


set_option backward.privateInPublic true
@[expose] public section

/-! Smooth compact spectral tests supported strictly inside (0,infinity)
are genuinely dense for the actual KL spectral measure. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ArtinMatthews

theorem spectral_L2_toLp_tendsto_of_dominated {μ : Measure ℝ}
    (f : ℕ → ℝ → ℂ) (hf : ∀ n, MemLp (f n) 2 μ) (g : ℝ → ℂ) (hg : MemLp g 2 μ)
    (B : ℝ → ℝ) (hB : Integrable B μ)
    (hbound : ∀ n, ∀ᵐ t ∂μ, ‖f n t-g t‖^2 ≤ B t)
    (hpoint : ∀ᵐ t ∂μ, Tendsto (fun n => f n t) atTop (𝓝 (g t))) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hI : Tendsto (fun n => ∫ t : ℝ, ‖f n t-g t‖^2 ∂μ) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => ∫ t : ℝ, ‖f n t-g t‖^2 ∂μ) atTop (𝓝 (∫ _ : ℝ, (0 : ℝ) ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence B
      · intro n
        exact ((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2
      · exact hB
      · intro n
        filter_upwards [hbound n] with t ht
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact ht
      · filter_upwards [hpoint] with t ht
        simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
          (ht.sub_const (g t)).norm.pow 2
    simpa only [integral_zero] using hh
  have hsq (n : ℕ) : ‖(hf n).toLp (f n)-hg.toLp g‖^2 = ∫ t : ℝ, ‖f n t-g t‖^2 ∂μ := by
    rw [← (hf n).toLp_sub hg,spectral_toLp_norm_sq]
    rfl
  have heq (n : ℕ) : Real.sqrt (∫ t : ℝ, ‖f n t-g t‖^2 ∂μ) = ‖(hf n).toLp (f n)-hg.toLp g‖ := by
    rw [← hsq]
    exact Real.sqrt_sq (norm_nonneg _)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,heq,Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hI

def spectralKLPositiveCutoff (n : ℕ) (t : ℝ) : ℝ :=
  Real.smoothTransition (((n : ℝ)+1)*t-1)

theorem spectralKLPositiveCutoff_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (fun t : ℝ => (spectralKLPositiveCutoff n t : ℂ)) := by
  have hc : ContDiff ℝ ∞ (spectralKLPositiveCutoff n) := by
    unfold spectralKLPositiveCutoff
    fun_prop
  exact Complex.ofRealCLM.contDiff.comp hc

theorem spectralKLPositiveCutoff_norm_le_one (n : ℕ) (t : ℝ) :
    ‖(spectralKLPositiveCutoff n t : ℂ)‖ ≤ 1 := by
  unfold spectralKLPositiveCutoff
  rw [Complex.norm_real,Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem spectralKLPositiveCutoff_tsupport (n : ℕ) :
    tsupport (fun t : ℝ => (spectralKLPositiveCutoff n t : ℂ)) ⊆ Ioi (0 : ℝ) := by
  have hN : 0 < (n : ℝ)+1 := by positivity
  have hs : tsupport (fun t : ℝ => (spectralKLPositiveCutoff n t : ℂ)) ⊆ Ici (1/((n : ℝ)+1)) := by
    unfold tsupport
    apply closure_minimal _ isClosed_Ici
    intro t ht
    by_contra hn
    have ht' : t < 1/((n : ℝ)+1) := lt_of_not_ge hn
    have harg : ((n : ℝ)+1)*t-1 ≤ 0 := by
      have hh := (lt_div_iff₀ hN).mp ht'
      nlinarith
    exact (Function.mem_support.mp ht) (by
      unfold spectralKLPositiveCutoff
      rw [Real.smoothTransition.zero_of_nonpos harg,Complex.ofReal_zero])
  intro t ht
  exact lt_of_lt_of_le (one_div_pos.mpr hN) (hs ht)

theorem spectralKLPositiveCutoff_eventually_one {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, spectralKLPositiveCutoff n t = 1 := by
  have hb : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have htop : Tendsto (fun n : ℕ => ((n : ℝ)+1)*t-1) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) (hb.atTop_mul_const ht)
  filter_upwards [htop.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
  exact Real.smoothTransition.one_of_one_le hn

theorem spectralKLPositiveCutoff_mul_properties (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (n : ℕ) :
    HasCompactSupport (fun t => (spectralKLPositiveCutoff n t : ℂ)*g t) ∧
      ContDiff ℝ ∞ (fun t => (spectralKLPositiveCutoff n t : ℂ)*g t) ∧
      tsupport (fun t => (spectralKLPositiveCutoff n t : ℂ)*g t) ⊆ Ioi (0 : ℝ) :=
  ⟨hgc.mul_left,(spectralKLPositiveCutoff_contDiff n).mul hg,
    tsupport_mul_subset_left.trans (spectralKLPositiveCutoff_tsupport n)⟩

theorem spectralKLPositiveCutoff_toLp_tendsto (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) :
    Tendsto (fun n : ℕ => (spectralKLSpectralMeasure_memLp_compact
      (fun t => (spectralKLPositiveCutoff n t : ℂ)*g t)
      ((spectralKLPositiveCutoff_contDiff n).mul hg).continuous hgc.mul_left).toLp
        (fun t => (spectralKLPositiveCutoff n t : ℂ)*g t)) atTop
      (𝓝 ((spectralKLSpectralMeasure_memLp_compact g hg.continuous hgc).toLp g)) := by
  have hgm := spectralKLSpectralMeasure_memLp_compact g hg.continuous hgc
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
  · filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [spectralKLPositiveCutoff_eventually_one ht] with n hn
    simp [hn]

theorem spectralKLSpectralMeasure_dense_positive_smooth :
    Dense {u : Lp ℂ 2 spectralKLSpectralMeasure | ∃ g : ℝ → ℂ,
      u =ᵐ[spectralKLSpectralMeasure] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
        tsupport g ⊆ Ioi (0 : ℝ)} := by
  have hd : Dense {u : Lp ℂ 2 spectralKLSpectralMeasure | ∃ g : ℝ → ℂ,
      u =ᵐ[spectralKLSpectralMeasure] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
    Lp.dense_hasCompactSupport_contDiff (by norm_num)
  have hs : {u : Lp ℂ 2 spectralKLSpectralMeasure | ∃ g : ℝ → ℂ,
      u =ᵐ[spectralKLSpectralMeasure] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} ⊆
      closure {u : Lp ℂ 2 spectralKLSpectralMeasure | ∃ g : ℝ → ℂ,
        u =ᵐ[spectralKLSpectralMeasure] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
          tsupport g ⊆ Ioi (0 : ℝ)} := by
    intro u hu
    obtain ⟨g,hug,hgc,hg⟩ := hu
    have hmeq : (spectralKLSpectralMeasure_memLp_compact g hg.continuous hgc).toLp g = u := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp _).trans hug.symm
    rw [← hmeq]
    apply mem_closure_of_tendsto (spectralKLPositiveCutoff_toLp_tendsto g hg hgc)
    apply Filter.Eventually.of_forall
    intro n
    obtain ⟨hc,hdiff,hpos⟩ := spectralKLPositiveCutoff_mul_properties g hg hgc n
    exact ⟨_,MemLp.coeFn_toLp _,hc,hdiff,hpos⟩
  intro u
  exact (closure_minimal hs isClosed_closure) (hd u)

end ArtinMatthews
