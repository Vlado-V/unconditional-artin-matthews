module

public import ArtinMatthews.SpectralKLPoleFactor


set_option backward.privateInPublic true
@[expose] public section

/-! Distributional normalization on the positive spectral half-line.
Continuity and compact support suffice, so smooth test functions are included. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology

namespace ArtinMatthews

theorem schlafliBesselK_product_imaginary_mellin_integrable (t v ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^((ε : ℂ)-1)*
      schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((v : ℂ)*Complex.I) x)
      (Ioi (0 : ℝ)) := by
  exact schlafliBesselK_product_mellin_integrable_of_re_gt _ _ _ (by simpa using hε)

theorem schlafliBesselK_product_mellin_test_integrable (t ε : ℝ) (hε : 0 < ε)
    (f : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun v : ℝ => f v *
      (∫ x in Ioi (0 : ℝ), (x : ℂ)^((ε : ℂ)-1)*
        schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((v : ℂ)*Complex.I) x)) := by
  have hA : Continuous (fun v : ℝ => spectralKLRegularAmplitude t (ε,v)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    exact (spectralKLRegularAmplitude_continuousAt t ε v hε.le (Or.inl hε)).comp
      (by fun_prop : ContinuousAt (fun v : ℝ => (ε,v)) v)
  have hP : Continuous (fun v : ℝ => (spectralPoissonPeak ε (v-t) : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    apply Continuous.div continuous_const (by fun_prop)
    intro v
    exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hε) (sq_nonneg _))
  have hi : Integrable (fun v : ℝ =>
      (f v*(spectralPoissonPeak ε (v-t) : ℂ))*spectralKLRegularAmplitude t (ε,v)) :=
    ((hf.mul hP).mul hA).integrable_of_hasCompactSupport ((hfc.mul_right).mul_right)
  convert hi using 1
  funext v
  rw [schlafliBesselK_product_mellin_closed _ _ _ (by simpa using hε)]
  change f v * spectralKProductClosedValue ((t : ℂ)*Complex.I) ((v : ℂ)*Complex.I) (ε : ℂ) = _
  rw [spectralKLRegularAmplitude_factor t ε v hε,Complex.real_smul]
  ring

theorem spectralKLRegularAmplitude_test_bound (t : ℝ) (ht : 0 < t)
    (f : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hpos : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Icc (0 : ℝ) 1, ∀ v : ℝ,
      ‖spectralKLRegularAmplitude t (ε,v)*f v‖ ≤ C := by
  have hcomp : IsCompact (Icc (0 : ℝ) 1 ×ˢ tsupport f) := isCompact_Icc.prod hfc.isCompact
  have hcont : ContinuousOn (fun p : ℝ × ℝ => spectralKLRegularAmplitude t p*f p.2)
      (Icc (0 : ℝ) 1 ×ˢ tsupport f) := by
    apply ContinuousOn.mul
    · intro p hp
      exact (spectralKLRegularAmplitude_continuousAt t p.1 p.2 hp.1.1
        (Or.inr (ne_of_gt (add_pos ht (hpos hp.2))))).continuousWithinAt
    · exact (hf.comp continuous_snd).continuousOn
  obtain ⟨C,hC⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro ε hε v
  by_cases hv : v ∈ tsupport f
  · exact (hC (ε,v) ⟨hε,hv⟩).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hv,mul_zero,norm_zero]
    exact le_trans zero_le_one (le_max_right _ _)

theorem spectralKLRegularAmplitude_test_continuous (t ε : ℝ) (hε : 0 < ε)
    (f : ℝ → ℂ) (hf : Continuous f) :
    Continuous (fun v : ℝ => spectralKLRegularAmplitude t (ε,v)*f v) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  apply ContinuousAt.mul
  · exact (spectralKLRegularAmplitude_continuousAt t ε v hε.le (Or.inl hε)).comp
      (by fun_prop : ContinuousAt (fun v : ℝ => (ε,v)) v)
  · exact hf.continuousAt

theorem spectralKLRegularAmplitude_test_tail_bound (t : ℝ) (ht : 0 < t)
    (f : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hpos : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ →
      ∀ v : ℝ, δ ≤ |v-t| →
        ‖spectralPoissonPeak ε (v-t) • (spectralKLRegularAmplitude t (ε,v)*f v)‖ ≤
          C*ε/δ^2 := by
  obtain ⟨C,hC,hbound⟩ := spectralKLRegularAmplitude_test_bound t ht f hf hfc hpos
  refine ⟨C,hC,?_⟩
  intro ε hε δ hδ v hv
  have hden : 0 < ε^2+(v-t)^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hε.1) (sq_nonneg _)
  have hd : δ^2 ≤ ε^2+(v-t)^2 := by
    nlinarith [sq_abs (v-t),sq_nonneg ε,abs_nonneg (v-t)]
  rw [norm_smul,Real.norm_of_nonneg (show 0 ≤ spectralPoissonPeak ε (v-t) by
    exact div_nonneg hε.1.le hden.le)]
  calc
    spectralPoissonPeak ε (v-t)*‖spectralKLRegularAmplitude t (ε,v)*f v‖ ≤
        spectralPoissonPeak ε (v-t)*C :=
      mul_le_mul_of_nonneg_left (hbound ε ⟨hε.1.le,hε.2.le⟩ v) (div_nonneg hε.1.le hden.le)
    _ ≤ C*ε/δ^2 := by
      unfold spectralPoissonPeak
      have hi : ε/(ε^2+(v-t)^2) ≤ ε/δ^2 := div_le_div_of_nonneg_left hε.1.le (sq_pos_of_pos hδ) hd
      exact (mul_le_mul_of_nonneg_right hi hC.le).trans_eq (by ring)

theorem spectralKLRegularAmplitude_test_uniform_tail (t : ℝ) (ht : 0 < t)
    (f : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hpos : tsupport f ⊆ Ioi (0 : ℝ)) (δ : ℝ) (hδ : 0 < δ) :
    TendstoUniformlyOn (fun ε v : ℝ =>
      spectralPoissonPeak ε (v-t) • (spectralKLRegularAmplitude t (ε,v)*f v))
      (fun _ => 0) (𝓝[>] (0 : ℝ)) {v : ℝ | δ ≤ |v-t|} := by
  obtain ⟨C,_hC,hbound⟩ := spectralKLRegularAmplitude_test_tail_bound t ht f hf hfc hpos
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  have hlim : Tendsto (fun ε : ℝ => C*ε/δ^2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ => C*ε/δ^2) 0 := by fun_prop
    simpa only [mul_zero,zero_div] using hc.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [hlim.eventually (Iio_mem_nhds hη),
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε hsmall
  intro v hv
  rw [dist_zero_left]
  exact (hbound ε hsmall δ hδ v hv).trans_lt hε

theorem spectralKLRegularAmplitude_test_limit (t : ℝ) (ht : 0 < t)
    (f : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hpos : tsupport f ⊆ Ioi (0 : ℝ)) :
    Tendsto (fun ε : ℝ => ∫ v : ℝ,
      spectralPoissonPeak ε (v-t) • (spectralKLRegularAmplitude t (ε,v)*f v))
      (𝓝[>] (0 : ℝ)) (𝓝 ((Real.pi^2/(2*t*Real.sinh (Real.pi*t)) : ℝ) • f t)) := by
  obtain ⟨C,_hC,hbound⟩ := spectralKLRegularAmplitude_test_bound t ht f hf hfc hpos
  have hcont : ContinuousAt (fun p : ℝ × ℝ => spectralKLRegularAmplitude t p*f p.2) (0,t) :=
    (spectralKLRegularAmplitude_continuousAt t 0 t le_rfl
      (Or.inr (ne_of_gt (add_pos ht ht)))).mul ((hf.comp continuous_snd).continuousAt)
  have hmeas : ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun u : ℝ => spectralKLRegularAmplitude t (ε,t+ε*u)*f (t+ε*u)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((spectralKLRegularAmplitude_test_continuous t ε hε f hf).comp
      (by fun_prop : Continuous (fun u : ℝ => t+ε*u))).aestronglyMeasurable
  have hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ v : ℝ,
      ‖spectralKLRegularAmplitude t (ε,v)*f v‖ ≤ C := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact hbound ε ⟨hε.1.le,hε.2.le⟩
  have hlim := spectralPoissonPeak_approximation t
    (fun p : ℝ × ℝ => spectralKLRegularAmplitude t p*f p.2) hcont hmeas C hb
  have heq : (Real.pi : ℂ)*(spectralKLRegularAmplitude t (0,t)*f t) =
      (Real.pi^2/(2*t*Real.sinh (Real.pi*t)) : ℝ) • f t := by
    rw [spectralKLRegularAmplitude_diagonal t ht,Complex.real_smul]
    push_cast
    ring
  simpa only [heq] using hlim

theorem schlafliBesselK_product_mellin_test_limit (t : ℝ) (ht : 0 < t)
    (f : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hpos : tsupport f ⊆ Ioi (0 : ℝ)) :
    Tendsto (fun ε : ℝ => ∫ v in Ioi (0 : ℝ), f v *
      (∫ x in Ioi (0 : ℝ), (x : ℂ)^((ε : ℂ)-1)*
        schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((v : ℂ)*Complex.I) x))
      (𝓝[>] (0 : ℝ)) (𝓝 ((Real.pi^2/(2*t*Real.sinh (Real.pi*t)) : ℝ) • f t)) := by
  apply (spectralKLRegularAmplitude_test_limit t ht f hf hfc hpos).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hclosed (v : ℝ) :
      (∫ x in Ioi (0 : ℝ), (x : ℂ)^((ε : ℂ)-1)*
        schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((v : ℂ)*Complex.I) x) =
      spectralPoissonPeak ε (v-t) • spectralKLRegularAmplitude t (ε,v) := by
    rw [schlafliBesselK_product_mellin_closed _ _ _ (by simpa using hε)]
    exact spectralKLRegularAmplitude_factor t ε v hε
  calc
    (∫ v : ℝ, spectralPoissonPeak ε (v-t) • (spectralKLRegularAmplitude t (ε,v)*f v)) =
        ∫ v in Ioi (0 : ℝ), spectralPoissonPeak ε (v-t) • (spectralKLRegularAmplitude t (ε,v)*f v) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro v hv
      have hn : v ∉ tsupport f := fun h => hv (hpos h)
      simp [image_eq_zero_of_notMem_tsupport hn]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      dsimp only
      rw [hclosed v,Complex.real_smul,Complex.real_smul]
      ring

end ArtinMatthews
