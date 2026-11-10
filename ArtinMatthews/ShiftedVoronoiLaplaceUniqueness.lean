module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Probability.Moments.ComplexMGF


set_option backward.privateInPublic true
@[expose] public section

/-!
# Uniqueness of half-line Laplace transforms

The finite-measure and signed-density arguments below adapt the proved sources
`OAI/Analysis/KadisonKastler/{LocalLaplaceUniqueness,RealLaplaceUniqueness,
ComplexLocalLaplace}.lean`. They use analyticity of moment generating functions
and uniqueness of characteristic functions. No unbuilt OAI module is imported.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace ArtinMatthews

private theorem finiteMeasure_eq_of_local_laplace {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {a : ℝ} (ha : 0 < a)
    (hμ : ∀ t ∈ Ioo (-a) a, Integrable (fun x : ℝ => Real.exp (t * x)) μ)
    (hν : ∀ t ∈ Ioo (-a) a, Integrable (fun x : ℝ => Real.exp (t * x)) ν)
    (heq : ∀ t ∈ Ioo (-a) a, mgf id μ t = mgf id ν t) : μ = ν := by
  let S : Set ℂ := {z | z.re ∈ Ioo (-a) a}
  have hμ' : Ioo (-a) a ⊆ interior (integrableExpSet id μ) := by
    apply interior_maximal hμ isOpen_Ioo
  have hν' : Ioo (-a) a ⊆ interior (integrableExpSet id ν) := by
    apply interior_maximal hν isOpen_Ioo
  have hf : AnalyticOnNhd ℂ (complexMGF id μ) S :=
    analyticOnNhd_complexMGF.mono (fun z hz => hμ' hz)
  have hg : AnalyticOnNhd ℂ (complexMGF id ν) S :=
    analyticOnNhd_complexMGF.mono (fun z hz => hν' hz)
  have hS : IsPreconnected S := (convex_Ioo (-a) a).linear_preimage Complex.reLm |>.isPreconnected
  have h0 : (0 : ℂ) ∈ S := by change -a < 0 ∧ 0 < a; constructor <;> linarith
  have hreal : ∃ᶠ t : ℝ in 𝓝[≠] 0, complexMGF id μ t = complexMGF id ν t := by
    have hi : Ioo (-a) a ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) ha
    have he : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ∈ Ioo (-a) a :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hi
    exact (he.mono fun t ht => by rw [complexMGF_ofReal, complexMGF_ofReal, heq t ht]).frequently
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] 0, complexMGF id μ z = complexMGF id ν z := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hx, he⟩ := hreal
    refine ⟨fun n => (xs n : ℂ), ?_, fun n => he n⟩
    rw [tendsto_nhdsWithin_iff] at hx ⊢
    constructor
    · simpa only [Function.comp_def, Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hx.1
    · simpa using hx.2
  have he := hf.eqOn_of_preconnected_of_frequently_eq hg hS h0 hfreq
  apply Measure.ext_of_charFun
  ext t
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  exact he (by simpa [S] using h0)


private theorem exp_positivePart_integrable (f : ℝ → ℝ) (hf : Measurable f) (s : ℝ)
    (hi : Integrable (fun t => Real.exp (s * t) * f t)) :
    Integrable (fun t => Real.exp (s * t) * max (f t) 0) := by
  apply hi.norm.mono' (by fun_prop)
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _))
      (Real.exp_pos _).le

private theorem exp_density_integrable (f : ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ t, 0 ≤ f t) (s : ℝ)
    (hi : Integrable (fun t => Real.exp (s * t) * f t)) :
    Integrable (fun t => Real.exp (s * t)) (volume.withDensity fun t => ENNReal.ofReal (f t)) := by
  apply (integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul, mul_comm] using hi

private theorem mgf_density (f : ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ t, 0 ≤ f t) (s : ℝ) :
    mgf id (volume.withDensity fun t => ENNReal.ofReal (f t)) s =
      ∫ t, Real.exp (s * t) * f t := by
  rw [mgf, integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by simp only [ENNReal.toReal_ofReal (hf0 t),
    smul_eq_mul, id_eq, mul_comm]

/-- A real coefficient with an open interval of exponential integrability is
zero almost everywhere if all its Laplace values in that interval vanish. -/
private theorem ae_zero_of_local_laplace (f : ℝ → ℝ) (hf : Measurable f)
    {a : ℝ} (ha : 0 < a)
    (hi : ∀ s ∈ Ioo (-a) a, Integrable (fun t => Real.exp (s * t) * f t))
    (hz : ∀ s ∈ Ioo (-a) a, (∫ t, Real.exp (s * t) * f t) = 0) :
    f =ᵐ[volume] 0 := by
  let p : ℝ → ℝ := fun t => max (f t) 0
  let q : ℝ → ℝ := fun t => max (-f t) 0
  have hp : Measurable p := hf.max measurable_const
  have hq : Measurable q := hf.neg.max measurable_const
  have hp0 (t) : 0 ≤ p t := le_max_right _ _
  have hq0 (t) : 0 ≤ q t := le_max_right _ _
  have hzero : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  have hpi (s) (hs : s ∈ Ioo (-a) a) : Integrable (fun t => Real.exp (s * t) * p t) :=
    exp_positivePart_integrable f hf s (hi s hs)
  have hqi (s) (hs : s ∈ Ioo (-a) a) : Integrable (fun t => Real.exp (s * t) * q t) := by
    apply exp_positivePart_integrable (fun t => -f t) hf.neg s
    apply (hi s hs).neg.congr
    filter_upwards [] with t
    simp only [Pi.neg_apply, mul_neg]
  have hpI : Integrable p := by simpa only [zero_mul, Real.exp_zero, one_mul] using hpi 0 hzero
  have hqI : Integrable q := by simpa only [zero_mul, Real.exp_zero, one_mul] using hqi 0 hzero
  let μ := volume.withDensity (fun t => ENNReal.ofReal (p t))
  let ν := volume.withDensity (fun t => ENNReal.ofReal (q t))
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hp.aestronglyMeasurable
      (Eventually.of_forall hp0)).mpr hpI)
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hq.aestronglyMeasurable
      (Eventually.of_forall hq0)).mpr hqI)
  have hdiff (t) : f t = p t - q t := by
    dsimp [p, q]
    rcases le_total 0 (f t) with ht | ht
    · rw [max_eq_left ht, max_eq_right (neg_nonpos.mpr ht), sub_zero]
    · rw [max_eq_right ht, max_eq_left (neg_nonneg.mpr ht)]
      ring
  have hm : μ = ν := finiteMeasure_eq_of_local_laplace ha
    (fun s hs => exp_density_integrable p hp hp0 s (hpi s hs))
    (fun s hs => exp_density_integrable q hq hq0 s (hqi s hs)) (by
      intro s hs
      rw [mgf_density p hp hp0, mgf_density q hq hq0]
      have he := hz s hs
      have hf' : (fun t => Real.exp (s * t) * f t) =
          (fun t => Real.exp (s * t) * p t - Real.exp (s * t) * q t) := by
        funext t
        rw [hdiff, mul_sub]
      rw [hf', integral_sub (hpi s hs) (hqi s hs)] at he
      exact sub_eq_zero.mp he)
  have he := (withDensity_eq_iff_of_sigmaFinite hp.ennreal_ofReal.aemeasurable
    hq.ennreal_ofReal.aemeasurable).mp hm
  filter_upwards [he] with t ht
  have hpq : p t = q t := by
    have hh := congrArg ENNReal.toReal ht
    simpa only [ENNReal.toReal_ofReal (hp0 t), ENNReal.toReal_ofReal (hq0 t)] using hh
  simpa only [Pi.zero_apply, hpq, sub_self] using hdiff t



private theorem ae_zero_of_complex_local_laplace (f : ℝ → ℂ) (hf : Measurable f)
    {a : ℝ} (ha : 0 < a)
    (hi : ∀ s ∈ Ioo (-a) a, Integrable (fun t => (Real.exp (s * t) : ℂ) * f t))
    (hz : ∀ s ∈ Ioo (-a) a, (∫ t, (Real.exp (s * t) : ℂ) * f t) = 0) :
    f =ᵐ[volume] 0 := by
  have hre : (fun t => (f t).re) =ᵐ[volume] 0 := ae_zero_of_local_laplace _
    (Complex.continuous_re.measurable.comp hf) ha
    (fun s hs => by
      simpa only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero] using (hi s hs).re)
    (fun s hs => by
      have h := integral_re (hi s hs)
      change (∫ t, ((Real.exp (s * t) : ℂ) * f t).re) =
        (∫ t, (Real.exp (s * t) : ℂ) * f t).re at h
      rw [hz s hs] at h
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Complex.zero_re] using h)
  have him : (fun t => (f t).im) =ᵐ[volume] 0 := ae_zero_of_local_laplace _
    (Complex.continuous_im.measurable.comp hf) ha
    (fun s hs => by
      simpa only [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero] using (hi s hs).im)
    (fun s hs => by
      have h := integral_im (hi s hs)
      change (∫ t, ((Real.exp (s * t) : ℂ) * f t).im) =
        (∫ t, (Real.exp (s * t) : ℂ) * f t).im at h
      rw [hz s hs] at h
      simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, Complex.zero_im] using h)
  filter_upwards [hre, him] with t ht_re ht_im
  exact Complex.ext ht_re ht_im

/-- Continuous functions on the positive half-line are determined by their
Laplace transforms on any real tail on which both transforms converge. No
measurability hypothesis outside the positive half-line is needed. -/
theorem eqOn_Ioi_of_laplace_eq (f g : ℝ → ℂ)
    (hf : ContinuousOn f (Ioi 0)) (hg : ContinuousOn g (Ioi 0)) (S : ℝ)
    (hfi : ∀ t : ℝ, S < t →
      IntegrableOn (fun y => f y * Complex.exp (-(t * y : ℝ))) (Ioi 0))
    (hgi : ∀ t : ℝ, S < t →
      IntegrableOn (fun y => g y * Complex.exp (-(t * y : ℝ))) (Ioi 0))
    (heq : ∀ t : ℝ, S < t →
      (∫ y in Ioi 0, f y * Complex.exp (-(t * y : ℝ))) =
        ∫ y in Ioi 0, g y * Complex.exp (-(t * y : ℝ))) :
    EqOn f g (Ioi 0) := by
  classical
  let T := S + 2
  let F : ℝ → ℂ := (Ioi 0).indicator
    (fun y => (f y - g y) * Complex.exp (-(T * y : ℝ)))
  have hF : Measurable F := by
    change Measurable ((Ioi 0).piecewise
      (fun y => (f y - g y) * Complex.exp (-(T * y : ℝ))) (fun _ => 0))
    exact ((hf.sub hg).mul (by fun_prop)).measurable_piecewise
      continuousOn_const measurableSet_Ioi
  have hscalar (s y : ℝ) :
      (Real.exp (s * y) : ℂ) * Complex.exp (-(T * y : ℝ)) =
        Complex.exp (-((T - s) * y : ℝ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hshift (s : ℝ) :
      (fun y => (Real.exp (s * y) : ℂ) * F y) = (Ioi 0).indicator
        (fun y => (f y - g y) * Complex.exp (-((T - s) * y : ℝ))) := by
    funext y
    by_cases hy : y ∈ Ioi 0
    · simp only [F, indicator_of_mem hy]
      rw [← hscalar]
      ring
    · simp only [F, indicator_of_notMem hy, mul_zero]
  have hzero : F =ᵐ[volume] 0 := ae_zero_of_complex_local_laplace F hF
    (a := 1) (by norm_num) (by
      intro s hs
      rw [hshift, integrable_indicator_iff measurableSet_Ioi]
      have hTs : S < T - s := by dsimp [T]; linarith [hs.2]
      have hi := (hfi (T - s) hTs).sub (hgi (T - s) hTs)
      change IntegrableOn (fun y => f y * Complex.exp (-((T - s) * y : ℝ)) -
        g y * Complex.exp (-((T - s) * y : ℝ))) (Ioi 0) at hi
      convert hi using 1
      funext y
      exact sub_mul _ _ _) (by
      intro s hs
      rw [hshift, integral_indicator measurableSet_Ioi]
      have hTs : S < T - s := by dsimp [T]; linarith [hs.2]
      have hsub : (fun y => (f y - g y) * Complex.exp (-((T - s) * y : ℝ))) =
          (fun y => f y * Complex.exp (-((T - s) * y : ℝ)) -
            g y * Complex.exp (-((T - s) * y : ℝ))) := funext (fun y => sub_mul _ _ _)
      rw [hsub, integral_sub (hfi (T - s) hTs) (hgi (T - s) hTs), heq (T - s) hTs, sub_self])
  have hfg : f =ᵐ[volume.restrict (Ioi 0)] g := by
    filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem measurableSet_Ioi] with y hFy hy
    have hprod : (f y - g y) * Complex.exp (-(T * y : ℝ)) = 0 := by
      simpa only [F, indicator_of_mem hy, Pi.zero_apply] using hFy
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (Complex.exp_ne_zero _))
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hfg isOpen_Ioi hf hg

end ArtinMatthews
