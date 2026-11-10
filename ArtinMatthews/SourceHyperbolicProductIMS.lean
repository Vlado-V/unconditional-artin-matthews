module

public import ArtinMatthews.SourceHyperbolicProductEnergy
public import ArtinMatthews.SourceHyperbolicProductMulEnergy
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem productPartial_ofReal {η : ProductSpace ι → ℝ} {p : ProductSpace ι}
    (hη : DifferentiableAt ℝ η p) (i : ι) (j : Fin 3) :
    productPartial (fun x => (η x : ℂ)) i j p =
      (fderiv ℝ η p (productDirection i j) : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp p hη.hasFDerivAt
  change HasFDerivAt (fun x => (η x : ℂ)) _ p at h
  rw [productPartial, h.fderiv]
  rfl

theorem productGradientEnergy_real_mul_ims
    {η : ProductSpace ι → ℝ} {W : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hη : DifferentiableAt ℝ η p) (hW : DifferentiableAt ℝ W p) :
    productGradientEnergy (fun x => (η x : ℂ) * W x) p =
      (productGradientPair (fun x => (η x : ℂ) ^ 2 * W x) W p).re +
        ‖W p‖ ^ 2 * productGradientEnergy (fun x => (η x : ℂ)) p := by
  let e : ProductSpace ι → ℂ := fun x => (η x : ℂ)
  have he : DifferentiableAt ℝ e p := Complex.ofRealCLM.differentiableAt.comp p hη
  have hpartial (i : ι) (j : Fin 3) :
      ‖productPartial (fun x => (η x : ℂ) * W x) i j p‖ ^ 2 =
        (star (productPartial (fun x => (η x : ℂ) ^ 2 * W x) i j p) *
          productPartial W i j p).re +
        ‖W p‖ ^ 2 * ‖productPartial (fun x => (η x : ℂ)) i j p‖ ^ 2 := by
    have hsq : (fun x => (η x : ℂ) ^ 2 * W x) = (fun x => (e x * e x) * W x) := by
      funext x
      simp only [e, pow_two]
    rw [hsq, productPartial_mul he hW,
      productPartial_mul (f := fun x => e x * e x) (he.mul he) hW,
      productPartial_mul he he]
    dsimp only [e]
    simp only [productPartial_ofReal hη]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hpair :
      (productGradientPair (fun x => (η x : ℂ) ^ 2 * W x) W p).re =
        ∑ i, (p i 2) ^ 2 * ∑ j : Fin 3,
          (star (productPartial (fun x => (η x : ℂ) ^ 2 * W x) i j p) *
            productPartial W i j p).re := by
    simp only [productGradientPair, ← Complex.ofReal_pow, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hsplit (i : ι) :
      (p i 2) ^ 2 * ∑ j : Fin 3,
          ‖productPartial (fun x => (η x : ℂ) * W x) i j p‖ ^ 2 =
        (p i 2) ^ 2 * (∑ j : Fin 3,
          (star (productPartial (fun x => (η x : ℂ) ^ 2 * W x) i j p) *
            productPartial W i j p).re) +
        ‖W p‖ ^ 2 * ((p i 2) ^ 2 * ∑ j : Fin 3,
          ‖productPartial (fun x => (η x : ℂ)) i j p‖ ^ 2) := by
    simp_rw [hpartial, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hpair]
  simp only [productGradientEnergy, hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]

end
end ArtinMatthews.SourceHyperbolicGreen
