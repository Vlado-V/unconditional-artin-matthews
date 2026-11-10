module

public import ArtinMatthews.SourceHyperbolicHardyCalculus
public import ArtinMatthews.SourceHyperbolicProductGreen
public import ArtinMatthews.SourceHyperbolicHardyIBP
public import ArtinMatthews.SourceHyperbolicHardyIntegral
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

def productVerticalEnergy (f : ProductSpace ι → ℂ) (p : ProductSpace ι) : ℝ :=
  ∑ i, ‖productVertical f i p‖^2

def productHardyRemainder (f : ProductSpace ι → ℂ) (p : ProductSpace ι) : ℝ :=
  ∑ i, ‖productVertical f i p - f p‖^2

theorem product_radial_density_divergence {f : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hf : ContDiffAt ℝ 1 f p) (hp : p ∈ productUpper ι) :
    (∑ i, productPartial (productWeightedValue f i) i 2 p) =
      productComplexDensity p * (productRadial f p - 2 * Fintype.card ι * f p) := by
  simp only [productWeightedValue_divergence hf hp, productRadial, Finset.mul_sum,
    mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem product_hardy_direction_identity {f : ProductSpace ι → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ productUpper ι) (i : ι) :
    (∫ p, ‖productVertical f i p - f p‖^2 ∂productVolume ι) =
      (∫ p, ‖productVertical f i p‖^2 ∂productVolume ι) -
        ∫ p, ‖f p‖^2 ∂productVolume ι := by
  have hff := hardy_norm_sq_integrable hf.continuous hc hsupp
  have hVV := hardy_norm_sq_integrable (hardyVertical_continuous hf i)
    (hardyVertical_compact hc i) ((hardyVertical_support i).trans hsupp)
  have hfV : Integrable (fun p => (star (f p) * productVertical f i p).re) (productVolume ι) := by
    simpa only [RCLike.re_eq_complex_re] using
      (hardy_pair_integrable hf.continuous (hardyVertical_continuous hf i) hc hsupp).re
  have he (p : ProductSpace ι) : ‖productVertical f i p - f p‖^2 =
      ‖productVertical f i p‖^2 + ‖f p‖^2 - 2 * (star (f p) * productVertical f i p).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    simp only [Complex.star_def, mul_comm]
  calc
    _ = ∫ p, ‖productVertical f i p‖^2 + ‖f p‖^2 -
        2 * (star (f p) * productVertical f i p).re ∂productVolume ι := by
      exact integral_congr_ae (Eventually.of_forall he)
    _ = (∫ p, ‖productVertical f i p‖^2 ∂productVolume ι) +
        (∫ p, ‖f p‖^2 ∂productVolume ι) -
        2 * ∫ p, (star (f p) * productVertical f i p).re ∂productVolume ι := by
      simpa only [Pi.add_apply, integral_add hVV hff, integral_const_mul] using
        integral_sub (hVV.add hff) (hfV.const_mul 2)
    _ = _ := by rw [product_hardy_cross_real hf hc hsupp i]; ring

theorem productVerticalEnergy_integrable {f : ProductSpace ι → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ productUpper ι) :
    Integrable (productVerticalEnergy f) (productVolume ι) := by
  apply integrable_finsetSum
  intro i _
  exact hardy_norm_sq_integrable (hardyVertical_continuous hf i)
    (hardyVertical_compact hc i) ((hardyVertical_support i).trans hsupp)

theorem productHardyRemainder_integrable {f : ProductSpace ι → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ productUpper ι) :
    Integrable (productHardyRemainder f) (productVolume ι) := by
  apply integrable_finsetSum
  intro i _
  apply hardy_norm_sq_integrable ((hardyVertical_continuous hf i).sub hf.continuous)
    ((hardyVertical_compact hc i).sub hc)
  exact (tsupport_sub (productVertical f i) f).trans (Set.union_subset ((hardyVertical_support i).trans hsupp) hsupp)

theorem product_hardy_identity {f : ProductSpace ι → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ productUpper ι) :
    (∫ p, productVerticalEnergy f p ∂productVolume ι) =
      (Fintype.card ι : ℝ) * (∫ p, ‖f p‖^2 ∂productVolume ι) +
        ∫ p, productHardyRemainder f p ∂productVolume ι := by
  have hV (i : ι) := hardy_norm_sq_integrable (hardyVertical_continuous hf i)
    (hardyVertical_compact hc i) ((hardyVertical_support i).trans hsupp)
  have hR (i : ι) : Integrable (fun p => ‖productVertical f i p - f p‖^2) (productVolume ι) := by
    apply hardy_norm_sq_integrable ((hardyVertical_continuous hf i).sub hf.continuous)
      ((hardyVertical_compact hc i).sub hc)
    exact (tsupport_sub (productVertical f i) f).trans (Set.union_subset ((hardyVertical_support i).trans hsupp) hsupp)
  simp only [productVerticalEnergy, productHardyRemainder]
  rw [integral_finsetSum _ (fun i _ => hV i), integral_finsetSum _ (fun i _ => hR i)]
  simp_rw [product_hardy_direction_identity hf hc hsupp]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem product_hardy_inequality {f : ProductSpace ι → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ productUpper ι) :
    (Fintype.card ι : ℝ) * (∫ p, ‖f p‖^2 ∂productVolume ι) ≤
      ∫ p, productVerticalEnergy f p ∂productVolume ι := by
  rw [product_hardy_identity hf hc hsupp]
  apply le_add_of_nonneg_right
  apply integral_nonneg_of_ae
  exact Eventually.of_forall fun p => Finset.sum_nonneg (fun i _ => sq_nonneg ‖productVertical f i p - f p‖)

theorem product_radial_cross_real {f : ProductSpace ι → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ productUpper ι) :
    (∫ p, (star (f p) * productRadial f p).re ∂productVolume ι) =
      (Fintype.card ι : ℝ) * (∫ p, ‖f p‖^2 ∂productVolume ι) := by
  have hI (i : ι) : Integrable (fun p => (star (f p) * productVertical f i p).re) (productVolume ι) := by
    simpa only [RCLike.re_eq_complex_re] using
      (hardy_pair_integrable hf.continuous (hardyVertical_continuous hf i) hc hsupp).re
  simp only [productRadial, Finset.mul_sum, Complex.re_sum]
  rw [integral_finsetSum _ (fun i _ => hI i)]
  simp only [product_hardy_cross_real hf hc hsupp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem product_hardy_inequality_on {f : ProductSpace ι → ℂ}
    (hf : ContDiffOn ℝ 1 f (productUpper ι)) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ productUpper ι) :
    (Fintype.card ι : ℝ) * (∫ p, ‖f p‖^2 ∂productVolume ι) ≤
      ∫ p, productVerticalEnergy f p ∂productVolume ι := by
  apply product_hardy_inequality _ hc hsupp
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ productUpper ι
  · exact (hf p hp).contDiffAt ((productUpper_isOpen ι).mem_nhds hp)
  · have hn : p ∉ tsupport f := fun h => hp (hsupp h)
    exact (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ProductSpace ι => (0 : ℂ)) p).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hn)

end
end ArtinMatthews.SourceHyperbolicGreen
