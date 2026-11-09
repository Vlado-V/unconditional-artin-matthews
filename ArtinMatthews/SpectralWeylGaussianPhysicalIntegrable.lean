module

public import ArtinMatthews.SpectralWeylGaussianAbsolute


set_option backward.privateInPublic true
@[expose] public section

/-! Actual Gaussian modulus/physical absolute convergence on the two
heights.  L1 compact tests and the cosine-free radial Gaussian bound
supply all Fubini hypotheses. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

def spectralWeylGaussianPhysicalIntegrand (s t p : ℝ) (f g : ℝ → ℂ)
    (q : (ℝ × ℝ) × ℝ) : ℂ :=
  Complex.exp (-(p : ℂ)*(q.2 : ℂ)^2)*(q.2 : ℂ)*
    (spectralWeylDimensionlessKernel s t q.2 q.1.1 q.1.2 : ℂ)*f q.1.2*star (g q.1.1)

theorem spectralWeylGaussianPhysicalIntegrand_measurable (s t p : ℝ) (f g : ℝ → ℂ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (spectralWeylGaussianPhysicalIntegrand s t p f g) := by
  have he : Measurable (fun q : (ℝ × ℝ) × ℝ => Complex.exp (-(p : ℂ)*(q.2 : ℂ)^2)*(q.2 : ℂ)) := by fun_prop
  unfold spectralWeylGaussianPhysicalIntegrand
  exact ((he.mul (Complex.continuous_ofReal.measurable.comp
    (spectralWeylDimensionlessKernel_joint_measurable s t))).mul
      (hf.comp (measurable_snd.comp measurable_fst))).mul
        ((continuous_star.measurable.comp hg).comp (measurable_fst.comp measurable_fst))

theorem spectralWeylGaussianPhysicalIntegrand_norm (s t p : ℝ) (f g : ℝ → ℂ)
    (q : (ℝ × ℝ) × ℝ) :
    ‖spectralWeylGaussianPhysicalIntegrand s t p f g q‖ =
      ‖Real.exp (-p*q.2^2)*q.2*spectralWeylDimensionlessKernel s t q.2 q.1.1 q.1.2‖*
        ‖f q.1.2‖*‖g q.1.1‖ := by
  rw [spectralWeylGaussianPhysicalIntegrand,spectralWeyl_gaussian_complex_real,
    norm_mul,norm_mul,norm_star,Complex.norm_real]

theorem spectralWeylGaussianPhysicalIntegrand_fiber_integrable {x z p : ℝ}
    (hx : 0 < x) (hz : 0 < z) (hp : 0 < p) (s t : ℝ) (f g : ℝ → ℂ)
    (hf : Measurable f) (hg : Measurable g) :
    Integrable (fun X : ℝ => spectralWeylGaussianPhysicalIntegrand s t p f g ((x,z),X))
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hi : Integrable (fun X : ℝ =>
      ‖Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z‖*‖f z‖*‖g x‖)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (((spectralWeylDimensionlessKernel_gaussian_integrable hx hz hp s t).norm.restrict).mul_const ‖f z‖).mul_const ‖g x‖
  have hm : Measurable (fun X : ℝ => spectralWeylGaussianPhysicalIntegrand s t p f g ((x,z),X)) :=
    (spectralWeylGaussianPhysicalIntegrand_measurable s t p f g hf hg).comp
      (measurable_const.prodMk measurable_id)
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards with X
  rw [spectralWeylGaussianPhysicalIntegrand_norm]

theorem spectralWeylGaussianPhysicalIntegrand_fiber_bound {x z p : ℝ}
    (hx : 0 < x) (hz : 0 < z) (hp : 0 < p) (s t : ℝ) (f g : ℝ → ℂ) :
    (∫ X in Ioi (0 : ℝ), ‖spectralWeylGaussianPhysicalIntegrand s t p f g ((x,z),X)‖) ≤
      Real.sqrt (Real.pi/p)*‖g x‖*‖f z‖ := by
  calc
    _ = (∫ X in Ioi (0 : ℝ),
        ‖Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z‖)*‖f z‖*‖g x‖ := by
      rw [← integral_mul_const,← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with X
      exact spectralWeylGaussianPhysicalIntegrand_norm s t p f g ((x,z),X)
    _ ≤ (Real.sqrt (Real.pi/p)*‖f z‖)*‖g x‖ := by
      gcongr
      exact spectralWeylDimensionlessKernel_gaussian_abs_bound hx hz hp s t
    _ = _ := by ring_nf

theorem spectralWeylGaussianPhysicalIntegrand_integrable {p : ℝ} (hp : 0 < p)
    (s t : ℝ) (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f spectralKLPhysicalMeasure) (hgi : Integrable g spectralKLPhysicalMeasure) :
    Integrable (spectralWeylGaussianPhysicalIntegrand s t p f g)
      ((spectralKLPhysicalMeasure.prod spectralKLPhysicalMeasure).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : AEStronglyMeasurable (spectralWeylGaussianPhysicalIntegrand s t p f g)
      ((spectralKLPhysicalMeasure.prod spectralKLPhysicalMeasure).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (spectralWeylGaussianPhysicalIntegrand_measurable s t p f g hf hg).aestronglyMeasurable
  have hpos : ∀ᵐ q ∂spectralKLPhysicalMeasure.prod spectralKLPhysicalMeasure, 0 < q.1 ∧ 0 < q.2 := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd))).mpr
    filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
    filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun z => z⁻¹)] with z hz
    exact ⟨hx,hz⟩
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [hpos] with q hq
    exact spectralWeylGaussianPhysicalIntegrand_fiber_integrable hq.1 hq.2 hp s t f g hf hg
  · have hb := (hgi.norm.mul_prod hfi.norm).const_mul (Real.sqrt (Real.pi/p))
    apply hb.mono' hm.norm.integral_prod_right'
    filter_upwards [hpos] with q hq
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    have hbq := spectralWeylGaussianPhysicalIntegrand_fiber_bound hq.1 hq.2 hp s t f g
    convert hbq using 1
    ring_nf

end ArtinMatthews
