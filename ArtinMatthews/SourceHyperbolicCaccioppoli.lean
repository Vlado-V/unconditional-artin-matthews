module

public import ArtinMatthews.SourceHyperbolicCaccioppoliAlgebra


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Energy absorption from the actual weak gradient identity tested against the square cutoff. -/
theorem product_caccioppoli_of_test
    (ν : Measure (ProductSpace ι)) (η : ProductSpace ι → ℝ) (u : ProductSpace ι → ℂ) (eigenvalue : ℂ)
    (hη : ∀ᵐ p ∂ν, DifferentiableAt ℝ η p)
    (hu : ∀ᵐ p ∂ν, DifferentiableAt ℝ u p)
    (hE : Integrable (fun p => η p ^ 2 * productGradientEnergy u p) ν)
    (hM : Integrable (fun p => η p ^ 2 * ‖u p‖ ^ 2) ν)
    (hB : Integrable (fun p => productGradientEnergy (fun q => (η q : ℂ)) p * ‖u p‖ ^ 2) ν)
    (hP : Integrable (productGradientPair (fun q => (η q : ℂ) ^ 2 * u q) u) ν)
    (hTest : (∫ p, productGradientPair (fun q => (η q : ℂ) ^ 2 * u q) u p ∂ν) =
      eigenvalue * ((∫ p, η p ^ 2 * ‖u p‖ ^ 2 ∂ν : ℝ) : ℂ)) :
    (∫ p, η p ^ 2 * productGradientEnergy u p ∂ν) ≤
      2 * ‖eigenvalue‖ * (∫ p, η p ^ 2 * ‖u p‖ ^ 2 ∂ν) +
        4 * (∫ p, productGradientEnergy (fun q => (η q : ℂ)) p * ‖u p‖ ^ 2 ∂ν) := by
  have hPre : Integrable (fun p =>
      (productGradientPair (fun q => (η q : ℂ) ^ 2 * u q) u p).re) ν := hP.re
  have hIntRe : (∫ p,
      (productGradientPair (fun q => (η q : ℂ) ^ 2 * u q) u p).re ∂ν) =
      (∫ p, productGradientPair (fun q => (η q : ℂ) ^ 2 * u q) u p ∂ν).re :=
    integral_re hP
  have hp : ∀ᵐ p ∂ν, η p ^ 2 * productGradientEnergy u p ≤
      2 * (productGradientPair (fun q => (η q : ℂ) ^ 2 * u q) u p).re +
        4 * (productGradientEnergy (fun q => (η q : ℂ)) p * ‖u p‖ ^ 2) := by
    filter_upwards [hη, hu] with p hηp hup
    simpa only [mul_assoc] using product_caccioppoli_pointwise hηp hup
  have he := integral_mono_ae hE ((hPre.const_mul 2).add (hB.const_mul 4)) hp
  change (∫ p, η p ^ 2 * productGradientEnergy u p ∂ν) ≤
    ∫ p, 2 * (productGradientPair (fun q => (η q : ℂ) ^ 2 * u q) u p).re +
      4 * (productGradientEnergy (fun q => (η q : ℂ)) p * ‖u p‖ ^ 2) ∂ν at he
  rw [integral_add (hPre.const_mul 2) (hB.const_mul 4), integral_const_mul,
    integral_const_mul, hIntRe, hTest] at he
  have hm : 0 ≤ ∫ p, η p ^ 2 * ‖u p‖ ^ 2 ∂ν := by
    have hzero := integral_mono_ae (integrable_zero _ _ ν) hM
      (Filter.Eventually.of_forall fun p => mul_nonneg (sq_nonneg (η p)) (sq_nonneg ‖u p‖))
    simpa using hzero
  have hr : (eigenvalue * ((∫ p, η p ^ 2 * ‖u p‖ ^ 2 ∂ν : ℝ) : ℂ)).re ≤
      ‖eigenvalue‖ * (∫ p, η p ^ 2 * ‖u p‖ ^ 2 ∂ν) := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
      mul_le_mul_of_nonneg_right (Complex.re_le_norm eigenvalue) hm
  nlinarith

/-- The weak eigen-equation in its original sesquilinear test convention gives Caccioppoli. -/
theorem product_caccioppoli_of_weak_test
    (ν : Measure (ProductSpace ι)) (η : ProductSpace ι → ℝ) (u : ProductSpace ι → ℂ) (eigenvalue : ℂ)
    (hη : ∀ᵐ p ∂ν, DifferentiableAt ℝ η p)
    (hu : ∀ᵐ p ∂ν, DifferentiableAt ℝ u p)
    (hE : Integrable (fun p => η p ^ 2 * productGradientEnergy u p) ν)
    (hM : Integrable (fun p => η p ^ 2 * ‖u p‖ ^ 2) ν)
    (hB : Integrable (fun p => productGradientEnergy (fun q => (η q : ℂ)) p * ‖u p‖ ^ 2) ν)
    (hP : Integrable (productGradientPair (fun q => (η q : ℂ) ^ 2 * u q) u) ν)
    (hWeak : (∫ p, productGradientPair (fun q => (η q : ℂ) ^ 2 * u q) u p ∂ν) =
      eigenvalue * (∫ p, star ((η p : ℂ) ^ 2 * u p) * u p ∂ν)) :
    (∫ p, η p ^ 2 * productGradientEnergy u p ∂ν) ≤
      2 * ‖eigenvalue‖ * (∫ p, η p ^ 2 * ‖u p‖ ^ 2 ∂ν) +
        4 * (∫ p, productGradientEnergy (fun q => (η q : ℂ)) p * ‖u p‖ ^ 2 ∂ν) := by
  apply product_caccioppoli_of_test ν η u eigenvalue hη hu hE hM hB hP
  rw [hWeak]
  congr 1
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    change star ((η p : ℂ) ^ 2 * u p) * u p = ((η p ^ 2 * ‖u p‖ ^ 2 : ℝ) : ℂ)
    have hu2 : star (u p) * u p = ((‖u p‖ ^ 2 : ℝ) : ℂ) := by
      simpa only [Complex.star_def, Complex.ofReal_pow] using! RCLike.conj_mul (u p)
    have hreal : star (η p : ℂ) = (η p : ℂ) := by simp only [Complex.star_def, Complex.conj_ofReal]
    rw [star_mul, star_pow, hreal]
    calc
      star (u p) * (η p : ℂ) ^ 2 * u p = (η p : ℂ) ^ 2 * (star (u p) * u p) := by ring
      _ = _ := by simp only [hu2, Complex.ofReal_mul, Complex.ofReal_pow]

end
end ArtinMatthews.SourceHyperbolicGreen
