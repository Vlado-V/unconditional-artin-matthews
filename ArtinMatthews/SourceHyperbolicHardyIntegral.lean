module

public import ArtinMatthews.SourceHyperbolicHardyIBP
public import ArtinMatthews.SourceHyperbolicProductMeasureGreen


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]


theorem hardy_integral_re {G : ProductSpace ι → ℂ}
    (hG : Integrable G (productVolume ι)) :
    (∫ p, G p ∂productVolume ι).re = ∫ p, (G p).re ∂productVolume ι := by
  simpa only [RCLike.re_eq_complex_re] using (integral_re hG).symm

theorem hardy_density_contDiffAt {p : ProductSpace ι} (hp : p ∈ productUpper ι) :
    ContDiffAt ℝ 1 (productComplexDensity (ι := ι)) p := by
  apply contDiffAt_prod
  intro i _
  have hH : ContDiffAt ℝ 1 (fun q : ProductSpace ι => (q i 2 : ℂ)) p :=
    (productHeightCLM i).contDiff.contDiffAt
  exact (hH.pow 3).fun_inv (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (productUpper_pos hp i).ne'))

theorem hardy_pair_integrable {φ ψ : ProductSpace ι → ℂ}
    (hφ : Continuous φ) (hψ : Continuous ψ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    Integrable (fun p => star (φ p) * ψ p) (productVolume ι) := by
  apply product_density_integrable
  have h := product_compact_star_mul_integrable hφ hc (F := fun p => productComplexDensity p * ψ p)
    (fun p hp => (hardy_density_contDiffAt (hsupp hp)).continuousAt.mul hψ.continuousAt)
  convert h using 1
  ext p
  ring

theorem hardy_norm_sq_integrable {φ : ProductSpace ι → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ productUpper ι) :
    Integrable (fun p => ‖φ p‖^2) (productVolume ι) := by
  have h := (hardy_pair_integrable hφ hφ hc hsupp).re
  simpa only [RCLike.re_eq_complex_re, Complex.star_def, Complex.conj_mul',
    ← Complex.ofReal_pow, Complex.ofReal_re] using h

theorem hardyVertical_continuous {f : ProductSpace ι → ℂ}
    (hf : ContDiff ℝ 1 f) (i : ι) : Continuous (productVertical f i) :=
  (productHeightCLM i).continuous.mul (hardyPartial_continuous hf i 2)

omit [Fintype ι] in
theorem hardyVertical_compact {f : ProductSpace ι → ℂ}
    (hc : HasCompactSupport f) (i : ι) : HasCompactSupport (productVertical f i) :=
  (hc.fderiv_apply ℝ (productDirection i 2)).mul_left

omit [Fintype ι] in
theorem hardyVertical_support {f : ProductSpace ι → ℂ} (i : ι) :
    tsupport (productVertical f i) ⊆ tsupport f :=
  tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ (productDirection i 2))

theorem product_hardy_ibp {f : ProductSpace ι → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ productUpper ι) (i : ι) :
    (∫ p, star (productVertical f i p) * f p ∂productVolume ι) =
      -(∫ p, star (f p) * (productVertical f i p - 2 * f p) ∂productVolume ι) := by
  rw [product_density_integral _ (fun p hp => by
    have hz : f p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hsupp h))
    rw [hz, mul_zero])]
  rw [product_density_integral _ (fun p hp => by
    have hz : f p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hsupp h))
    rw [hz, star_zero, zero_mul])]
  simp_rw [product_hardy_left_density hsupp, product_hardy_right_density hf hsupp]
  exact product_hardy_ibp_euclidean (fun p _ => hf.contDiffAt) hf hc hsupp i

theorem product_hardy_cross_real {f : ProductSpace ι → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ productUpper ι) (i : ι) :
    (∫ p, (star (f p) * productVertical f i p).re ∂productVolume ι) =
      ∫ p, ‖f p‖^2 ∂productVolume ι := by
  have hff := hardy_pair_integrable hf.continuous hf.continuous hc hsupp
  have hfV := hardy_pair_integrable hf.continuous (hardyVertical_continuous hf i) hc hsupp
  have hVf := hardy_pair_integrable (hardyVertical_continuous hf i) hf.continuous
    (hardyVertical_compact hc i) ((hardyVertical_support i).trans hsupp)
  have h := congrArg Complex.re (product_hardy_ibp hf hc hsupp i)
  have he : (fun p => star (f p) * (productVertical f i p - 2 * f p)) =
      (fun p => star (f p) * productVertical f i p - 2 * (star (f p) * f p)) := by
    funext p
    ring
  rw [he, integral_sub hfV (hff.const_mul 2), integral_const_mul] at h
  have hr : (∫ p, star (productVertical f i p) * f p ∂productVolume ι).re =
      ∫ p, (star (f p) * productVertical f i p).re ∂productVolume ι := by
    rw [hardy_integral_re hVf]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
  have hnorm : (∫ p, star (f p) * f p ∂productVolume ι).re =
      ∫ p, ‖f p‖^2 ∂productVolume ι := by
    rw [hardy_integral_re hff]
    simp only [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hr, Complex.neg_re, Complex.sub_re, Complex.mul_re,
    show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl,
    zero_mul, sub_zero, hnorm, hardy_integral_re hfV] at h
  linarith

end
end ArtinMatthews.SourceHyperbolicGreen
