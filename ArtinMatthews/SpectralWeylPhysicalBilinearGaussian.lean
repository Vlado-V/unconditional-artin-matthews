module

public import ArtinMatthews.SpectralWeylGaussianPhysicalIntegrable


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine unregularized compact physical orbital bilinear form
has the checked J/K Gaussian tests.  Moving the Gaussian outside is now
justified by actual absolute modulus/physical Fubini. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

def spectralWeylPhysicalIntegrand (s t : ℝ) (f g : ℝ → ℂ) (q : (ℝ × ℝ) × ℝ) : ℂ :=
  (spectralWeylDimensionlessKernel s t q.2 q.1.1 q.1.2 : ℂ)*f q.1.2*star (g q.1.1)

def spectralWeylPhysicalBilinear (s t : ℝ) (f g : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∫ q : ℝ × ℝ, spectralWeylPhysicalIntegrand s t f g (q,X)
    ∂spectralKLPhysicalMeasure.prod spectralKLPhysicalMeasure

theorem spectralWeylPhysicalIntegrand_measurable (s t : ℝ) (f g : ℝ → ℂ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (spectralWeylPhysicalIntegrand s t f g) := by
  unfold spectralWeylPhysicalIntegrand
  exact ((Complex.continuous_ofReal.measurable.comp
    (spectralWeylDimensionlessKernel_joint_measurable s t)).mul
      (hf.comp (measurable_snd.comp measurable_fst))).mul
        ((continuous_star.measurable.comp hg).comp (measurable_fst.comp measurable_fst))

theorem spectralWeylPhysicalBilinear_measurable (s t : ℝ) (f g : ℝ → ℂ)
    (hf : Measurable f) (hg : Measurable g) : Measurable (spectralWeylPhysicalBilinear s t f g) := by
  have hm := ((spectralWeylPhysicalIntegrand_measurable s t f g hf hg).comp measurable_swap).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

theorem spectralWeylGaussianPhysicalIntegrand_factor (s t p : ℝ) (f g : ℝ → ℂ)
    (q : (ℝ × ℝ) × ℝ) :
    spectralWeylGaussianPhysicalIntegrand s t p f g q =
      (Complex.exp (-(p : ℂ)*(q.2 : ℂ)^2)*(q.2 : ℂ))*spectralWeylPhysicalIntegrand s t f g q := by
  unfold spectralWeylGaussianPhysicalIntegrand spectralWeylPhysicalIntegrand
  ring_nf

theorem spectralWeylPhysicalBilinear_gaussian_integrable {p : ℝ} (hp : 0 < p)
    (s t : ℝ) (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f spectralKLPhysicalMeasure) (hgi : Integrable g spectralKLPhysicalMeasure) :
    IntegrableOn (fun X : ℝ => Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      spectralWeylPhysicalBilinear s t f g X) (Ioi (0 : ℝ)) := by
  have hi := spectralWeylGaussianPhysicalIntegrand_integrable hp s t f g hf hg hfi hgi
  apply hi.integral_prod_right.congr
  filter_upwards with X
  rw [spectralWeylPhysicalBilinear,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with q
  exact spectralWeylGaussianPhysicalIntegrand_factor s t p f g (q,X)

theorem spectralWeylPhysicalBilinear_gaussian_fubini {p : ℝ} (hp : 0 < p)
    (s t : ℝ) (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f spectralKLPhysicalMeasure) (hgi : Integrable g spectralKLPhysicalMeasure) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      spectralWeylPhysicalBilinear s t f g X) =
      ∫ x : ℝ, (∫ z : ℝ,
        ((∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z : ℝ) : ℂ)*
          f z ∂spectralKLPhysicalMeasure)*star (g x) ∂spectralKLPhysicalMeasure := by
  have hi := spectralWeylGaussianPhysicalIntegrand_integrable hp s t f g hf hg hfi hgi
  calc
    _ = ∫ X in Ioi (0 : ℝ), ∫ q : ℝ × ℝ,
        spectralWeylGaussianPhysicalIntegrand s t p f g (q,X)
          ∂spectralKLPhysicalMeasure.prod spectralKLPhysicalMeasure := by
      apply integral_congr_ae
      filter_upwards with X
      rw [spectralWeylPhysicalBilinear,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with q
      exact (spectralWeylGaussianPhysicalIntegrand_factor s t p f g (q,X)).symm
    _ = ∫ q : ℝ × ℝ, (∫ X in Ioi (0 : ℝ), spectralWeylGaussianPhysicalIntegrand s t p f g (q,X))
        ∂spectralKLPhysicalMeasure.prod spectralKLPhysicalMeasure :=
      (integral_integral_swap (f := fun (q : ℝ × ℝ) (X : ℝ) =>
        spectralWeylGaussianPhysicalIntegrand s t p f g (q,X)) hi).symm
    _ = ∫ x : ℝ, (∫ z : ℝ, (∫ X in Ioi (0 : ℝ),
        spectralWeylGaussianPhysicalIntegrand s t p f g ((x,z),X))
          ∂spectralKLPhysicalMeasure) ∂spectralKLPhysicalMeasure := integral_prod _ hi.integral_prod_left
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with z
      rw [← integral_complex_ofReal,← integral_mul_const,← integral_mul_const]
      simp_rw [spectralWeylGaussianPhysicalIntegrand,spectralWeyl_gaussian_complex_real]

theorem spectralWeylPhysicalBilinear_same_gaussian_J {p : ℝ} (hp : 1/4 < p)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = 1)
    (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*spectralWeylPhysicalBilinear s t f g X) =
      ∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
        (∫ r : ℝ, spectralWeylJMultiplier r X*spectralKLPhysicalAnalysisIntegral f r*
          star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure) := by
  rw [spectralWeylPhysicalBilinear_gaussian_fubini (by linarith : 0 < p) s t f g hf.measurable hg.measurable
    (spectralKLPhysical_compact_integrable f hf hfc hfp) (spectralKLPhysical_compact_integrable g hg hgc hgp)]
  exact spectralWeylGaussian_same_bilinear_J hp s t hs ht hst f g hf hfc hfp hg hgc hgp

theorem spectralWeylPhysicalBilinear_opposite_gaussian_K {p : ℝ} (hp : 1/4 < p)
    (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = -1)
    (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*spectralWeylPhysicalBilinear s t f g X) =
      ∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
        (∫ r : ℝ, spectralWeylKMultiplier r X*spectralKLPhysicalAnalysisIntegral f r*
          star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure) := by
  rw [spectralWeylPhysicalBilinear_gaussian_fubini (by linarith : 0 < p) s t f g hf.measurable hg.measurable
    (spectralKLPhysical_compact_integrable f hf hfc hfp) (spectralKLPhysical_compact_integrable g hg hgc hgp)]
  exact spectralWeylGaussian_opposite_bilinear_K hp s t hs ht hst f g hf hfc hfp hg hgc hgp

end ArtinMatthews
