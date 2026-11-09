module

public import ArtinMatthews.SpectralJForwardHolomorphic
public import ArtinMatthews.SpectralJForwardStripKernel
public import ArtinMatthews.SpectralJForwardTail


set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrary polynomial decay for the literal compact forward transform
through the closed strip |Im z| ≤ 3/4. -/
noncomputable section
open Set
open scoped ContDiff

namespace ArtinMatthews
open SourceSturm

private theorem spectral_positive_compact_support_Icc {f : ℝ → ℂ}
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∃ a b : ℝ, 0 < a ∧ tsupport f ⊆ Icc a b := by
  let K := insert (1 : ℝ) (tsupport f)
  have hK : IsCompact K := hc.insert 1
  obtain ⟨a,ha,hmin⟩ := hK.exists_isMinOn (insert_nonempty _ _) continuous_id.continuousOn
  obtain ⟨b,hb,hmax⟩ := hK.exists_isMaxOn (insert_nonempty _ _) continuous_id.continuousOn
  refine ⟨a,b,?_,?_⟩
  · rcases mem_insert_iff.mp ha with h | h
    · rw [h]
      exact one_pos
    · exact hp h
  · intro x hx
    exact ⟨hmin (mem_insert_of_mem _ hx),hmax (mem_insert_of_mem _ hx)⟩

theorem spectralJForwardTransform_strip_rapid (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ 3/4 →
      ‖spectralJForwardTransform f z‖ ≤ C/(1+|z.re|)^k := by
  obtain ⟨a,b,ha,hSupp⟩ := spectral_positive_compact_support_Icc hc hp
  obtain ⟨C,hC,hB⟩ := spectralJForwardKernel_strip_on_Icc (b := b) ha
  let D := C*sturmL1 ((sturmD^[k+3]) f)
  let K : Set ℂ := {z : ℂ | |z.re| ≤ 1 ∧ |z.im| ≤ 3/4}
  have hK₀ : IsClosed K :=
    (isClosed_le Complex.continuous_re.abs continuous_const).inter
      (isClosed_le Complex.continuous_im.abs continuous_const)
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset hK₀ (by
    intro z hz
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith only [hz.1,hz.2]))
  have hCont : ContinuousOn (spectralJForwardTransform f) K :=
    (spectralJForwardTransform_analyticOnNhd f hf.continuous hc hp).continuousOn.mono
      (fun z hz => lt_of_le_of_lt hz.2 (by norm_num))
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hCont
  let Ctot := max D (max M 0*2^k)
  have hCtot : 0 ≤ Ctot := (by positivity : 0 ≤ max M 0*2^k).trans (le_max_right _ _)
  refine ⟨Ctot,hCtot,?_⟩
  intro z hz
  by_cases hRe : 1 ≤ |z.re|
  · exact (spectralJForwardTransform_tail_of_kernel hf hc hp k 3 hRe hC.le
      (fun x hx => hB z hz hRe x (hSupp hx))).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hRe' : |z.re| ≤ 1 := (lt_of_not_ge hRe).le
    have hMz : ‖spectralJForwardTransform f z‖ ≤ max M 0 :=
      (hM z ⟨hRe',hz⟩).trans (le_max_left _ _)
    have hPow : (1+|z.re|)^k ≤ (2 : ℝ)^k :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hRe']) k
    apply (le_div_iff₀ (by positivity : 0 < (1+|z.re|)^k)).mpr
    exact (mul_le_mul hMz hPow (by positivity) (le_max_right _ _)).trans (le_max_right _ _)

theorem spectralJForwardTransform_real_rapid (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖spectralJForwardTransform f (t : ℂ)‖ ≤ C/(1+|t|)^k := by
  obtain ⟨C,hC,h⟩ := spectralJForwardTransform_strip_rapid f hf hc hp k
  refine ⟨C,hC,fun t => ?_⟩
  simpa only [Complex.ofReal_re] using h (t : ℂ) (by norm_num)

end ArtinMatthews
