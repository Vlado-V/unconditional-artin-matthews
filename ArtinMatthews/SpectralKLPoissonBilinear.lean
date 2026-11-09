module

public import ArtinMatthews.SpectralKLDistributionalOrthogonality


set_option backward.privateInPublic true
@[expose] public section

/-! The diagonal kernel limit integrated against a second compact spectral
test. Uniform bounds are derived on the actual compact Gamma amplitude. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectralKLRegularAmplitude_joint_continuousAt (t ε v : ℝ) (hε : 0 ≤ ε)
    (hn : 0 < ε ∨ t+v ≠ 0) :
    ContinuousAt (fun q : ℝ × (ℝ × ℝ) => spectralKLRegularAmplitude q.1 q.2) (t,ε,v) := by
  have hsum (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
      ContinuousAt (fun q : ℝ × (ℝ × ℝ) =>
        Complex.Gamma (((q.2.1 : ℂ)+(σ : ℂ)*((q.1 : ℂ)*Complex.I+(q.2.2 : ℂ)*Complex.I))/2)) (t,ε,v) := by
    apply ContinuousAt.comp (g := Complex.Gamma)
    · apply spectral_Gamma_continuousAt_nonneg_re
      · rcases hσ with rfl | rfl <;> simp <;> positivity
      · intro h
        rcases hn with he | hv
        · have hr := congrArg Complex.re h
          rcases hσ with rfl | rfl <;> simp at hr <;> linarith
        · have hi := congrArg Complex.im h
          rcases hσ with rfl | rfl <;> simp at hi <;> apply hv <;> linarith
    · fun_prop
  have hm := hsum (-1) (Or.inr rfl)
  have hp := hsum 1 (Or.inl rfl)
  have hm' : ContinuousAt (fun q : ℝ × (ℝ × ℝ) =>
      Complex.Gamma (((q.2.1 : ℂ)-(q.1 : ℂ)*Complex.I-(q.2.2 : ℂ)*Complex.I)/2)) (t,ε,v) := by
    convert hm using 1
    funext q
    congr 1
    push_cast
    ring
  have hp' : ContinuousAt (fun q : ℝ × (ℝ × ℝ) =>
      Complex.Gamma (((q.2.1 : ℂ)+(q.1 : ℂ)*Complex.I+(q.2.2 : ℂ)*Complex.I)/2)) (t,ε,v) := by
    convert hp using 1
    funext q
    congr 1
    push_cast
    ring
  have hshift (σ : ℝ) : ContinuousAt (fun q : ℝ × (ℝ × ℝ) =>
      Complex.Gamma (1+((q.2.1 : ℂ)+(σ : ℂ)*((q.1 : ℂ)*Complex.I-(q.2.2 : ℂ)*Complex.I))/2)) (t,ε,v) := by
    apply ContinuousAt.comp (g := Complex.Gamma)
    · apply spectral_Gamma_continuousAt_nonneg_re
      · simp
        positivity
      · intro h
        have hr := congrArg Complex.re h
        simp at hr
        linarith
    · fun_prop
  have hs1 := hshift 1
  have hs2 := hshift (-1)
  have hs1' : ContinuousAt (fun q : ℝ × (ℝ × ℝ) =>
      Complex.Gamma (1+((q.2.1 : ℂ)+(q.1 : ℂ)*Complex.I-(q.2.2 : ℂ)*Complex.I)/2)) (t,ε,v) := by
    convert hs1 using 1
    funext q
    congr 1
    push_cast
    ring
  have hs2' : ContinuousAt (fun q : ℝ × (ℝ × ℝ) =>
      Complex.Gamma (1+((q.2.1 : ℂ)-(q.1 : ℂ)*Complex.I+(q.2.2 : ℂ)*Complex.I)/2)) (t,ε,v) := by
    convert hs2 using 1
    funext q
    congr 1
    push_cast
    ring
  have hpow : ContinuousAt (fun q : ℝ × (ℝ × ℝ) => (2 : ℂ)^((q.2.1 : ℂ)-1)) (t,ε,v) := by
    exact (by fun_prop : ContinuousAt (fun q : ℝ × (ℝ × ℝ) => (q.2.1 : ℂ)-1) (t,ε,v)).const_cpow
      (Or.inl (by norm_num))
  have hi : ContinuousAt (fun q : ℝ × (ℝ × ℝ) => (Complex.Gamma ((q.2.1 : ℂ)+1))⁻¹) (t,ε,v) := by
    exact Complex.differentiable_one_div_Gamma.continuous.continuousAt.comp (by fun_prop)
  exact (((((hpow.mul hm').mul hp').mul hs1').mul hs2').mul hi)

theorem spectralPoissonPeak_integrable (ε t : ℝ) (hε : 0 < ε) :
    Integrable (fun v : ℝ => spectralPoissonPeak ε (v-t)) := by
  have hi : Integrable (fun v : ℝ => (spectralPoissonPeak ε (v-t) : ℂ)) :=
    Integrable.of_integral_ne_zero (by
      rw [spectralPoissonPeak_integral ε t hε]
      exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact hi.re

theorem spectralPoissonPeak_real_integral (ε t : ℝ) (hε : 0 < ε) :
    (∫ v : ℝ, spectralPoissonPeak ε (v-t)) = Real.pi := by
  apply Complex.ofReal_injective
  simpa only [integral_complex_ofReal] using spectralPoissonPeak_integral ε t hε

theorem spectralKLRegularAmplitude_two_test_bound
    (f g : ℝ → ℂ) (hg : Continuous g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfp : tsupport f ⊆ Ioi (0 : ℝ)) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ tsupport f, ∀ ε ∈ Icc (0 : ℝ) 1, ∀ v : ℝ,
      ‖spectralKLRegularAmplitude t (ε,v)*g v‖ ≤ C := by
  have hcomp : IsCompact (tsupport f ×ˢ (Icc (0 : ℝ) 1 ×ˢ tsupport g)) :=
    hfc.isCompact.prod (isCompact_Icc.prod hgc.isCompact)
  have hc : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      spectralKLRegularAmplitude q.1 q.2*g q.2.2)
      (tsupport f ×ˢ (Icc (0 : ℝ) 1 ×ˢ tsupport g)) := by
    apply ContinuousOn.mul
    · intro q hq
      exact (spectralKLRegularAmplitude_joint_continuousAt q.1 q.2.1 q.2.2 hq.2.1.1
        (Or.inr (ne_of_gt (add_pos (hfp hq.1) (hgp hq.2.2))))).continuousWithinAt
    · exact (hg.comp (continuous_snd.comp continuous_snd)).continuousOn
  obtain ⟨C,hC⟩ := hcomp.exists_bound_of_continuousOn hc
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro t ht ε hε v
  by_cases hv : v ∈ tsupport g
  · exact (hC (t,ε,v) ⟨ht,hε,hv⟩).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hv,mul_zero,norm_zero]
    exact zero_le_one.trans (le_max_right _ _)

theorem spectralKLRegularAmplitude_test_integral_bound (t ε C : ℝ) (hε : 0 < ε)
    (g : ℝ → ℂ) (hb : ∀ v : ℝ, ‖spectralKLRegularAmplitude t (ε,v)*g v‖ ≤ C) :
    ‖∫ v : ℝ, spectralPoissonPeak ε (v-t) • (spectralKLRegularAmplitude t (ε,v)*g v)‖ ≤
      Real.pi*C := by
  have hi := (spectralPoissonPeak_integrable ε t hε).mul_const C
  calc
    _ ≤ ∫ v : ℝ, spectralPoissonPeak ε (v-t)*C := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards with v
      have hp : 0 ≤ spectralPoissonPeak ε (v-t) := div_nonneg hε.le (by positivity)
      rw [norm_smul,Real.norm_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left (hb v) hp
    _ = _ := by rw [integral_mul_const,spectralPoissonPeak_real_integral ε t hε]

theorem spectralKLRegularAmplitude_fixed_pos_continuous (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun p : ℝ × ℝ => spectralKLRegularAmplitude p.1 (ε,p.2)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let H : ℝ × ℝ → ℝ × (ℝ × ℝ) := fun q => (q.1,ε,q.2)
  have hH : ContinuousAt H p := by fun_prop
  have hA := spectralKLRegularAmplitude_joint_continuousAt p.1 ε p.2 hε.le (Or.inl hε)
  exact ContinuousAt.comp (f := H) (g := fun q : ℝ × (ℝ × ℝ) => spectralKLRegularAmplitude q.1 q.2) hA hH

theorem spectralKLRegularAmplitude_bilinear_limit
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfp : tsupport f ⊆ Ioi (0 : ℝ)) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ, f t *
      ∫ v : ℝ, spectralPoissonPeak ε (v-t) • (spectralKLRegularAmplitude t (ε,v)*g v))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t : ℝ, ((Real.pi^2/(2*t*Real.sinh (Real.pi*t)) : ℝ) : ℂ)*(f t*g t))) := by
  obtain ⟨C,_hC,hbound⟩ := spectralKLRegularAmplitude_two_test_bound f g hg hfc hgc hfp hgp
  apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => ‖f t‖*(Real.pi*C))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hjoint : Continuous (fun p : ℝ × ℝ =>
        spectralPoissonPeak ε (p.2-p.1) • (spectralKLRegularAmplitude p.1 (ε,p.2)*g p.2)) := by
      have hA := spectralKLRegularAmplitude_fixed_pos_continuous ε hε
      have hP : Continuous (fun p : ℝ × ℝ => spectralPoissonPeak ε (p.2-p.1)) := by
        unfold spectralPoissonPeak
        apply Continuous.div continuous_const (by fun_prop)
        intro p
        exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hε) (sq_nonneg _))
      exact hP.smul (hA.mul (hg.comp continuous_snd))
    exact hf.aestronglyMeasurable.mul hjoint.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    filter_upwards with t
    by_cases ht : t ∈ tsupport f
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (spectralKLRegularAmplitude_test_integral_bound t ε C hε.1 g
          (hbound t ht ε ⟨hε.1.le,hε.2.le⟩)) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport ht]
  · exact (hf.integrable_of_hasCompactSupport hfc).norm.mul_const (Real.pi*C)
  · filter_upwards with t
    by_cases ht : t ∈ tsupport f
    · have hi := (spectralKLRegularAmplitude_test_limit t (hfp ht) g hg hgc hgp).const_mul (f t)
      convert hi using 1
      rw [Complex.real_smul]
      ring
    · simp only [image_eq_zero_of_notMem_tsupport ht,zero_mul,mul_zero]
      exact tendsto_const_nhds

end ArtinMatthews
