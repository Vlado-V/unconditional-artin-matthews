module

public import ArtinMatthews.SourceHyperbolicProductEnergy
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory
open scoped Topology ContDiff BigOperators Classical
noncomputable section

/-- The complete square giving the complex Caccioppoli absorption constants. -/
theorem caccioppoli_complex_square (a b : ℂ) :
    ‖a‖ ^ 2 ≤ 2 * (star (a + 2 * b) * a).re + 4 * ‖b‖ ^ 2 := by
  have he : 2 * (star (a + 2 * b) * a).re + 4 * ‖b‖ ^ 2 - ‖a‖ ^ 2 =
      ‖a + 2 * b‖ ^ 2 := by
    norm_num [Complex.sq_norm, Complex.normSq_apply, Complex.star_def,
      Complex.mul_re, Complex.mul_im]
    ring
  have hn := sq_nonneg ‖a + 2 * b‖
  linarith

theorem caccioppoli_cutoff_scalar (t : ℝ) (u a b : ℂ) :
    t ^ 2 * ‖a‖ ^ 2 ≤
      2 * (star ((t : ℂ) ^ 2 * a + 2 * (t : ℂ) * b * u) * a).re +
        4 * ‖b‖ ^ 2 * ‖u‖ ^ 2 := by
  have he : star ((t : ℂ) * a + 2 * (b * u)) * ((t : ℂ) * a) =
      star ((t : ℂ) ^ 2 * a + 2 * (t : ℂ) * b * u) * a := by
    simp only [Complex.star_def, map_add, map_mul, map_pow, Complex.conj_ofReal, map_ofNat]
    ring
  have h := caccioppoli_complex_square ((t : ℂ) * a) (b * u)
  rw [he] at h
  simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_assoc]
    using h

variable {ι : Type*} [Fintype ι]

/-- The actual coordinate partial derivative of the real-square cutoff test. -/
theorem productPartial_cutoff_square {η : ProductSpace ι → ℝ} {u : ProductSpace ι → ℂ}
    {p : ProductSpace ι} (hη : DifferentiableAt ℝ η p) (hu : DifferentiableAt ℝ u p)
    (i : ι) (j : Fin 3) :
    productPartial (fun q => (η q : ℂ) ^ 2 * u q) i j p =
      (η p : ℂ) ^ 2 * productPartial u i j p +
        2 * (η p : ℂ) * productPartial (fun q => (η q : ℂ)) i j p * u p := by
  have hηC : DifferentiableAt ℝ (fun q => (η q : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p hη
  have hD := ((hηC.hasFDerivAt.pow 2).mul hu.hasFDerivAt).fderiv
  have he := congrArg (fun L : ProductSpace ι →L[ℝ] ℂ => L (productDirection i j)) hD
  unfold productPartial
  convert he using 1
  norm_num [add_apply, smul_apply, smul_eq_mul, two_smul]
  ring

/-- Pointwise Caccioppoli absorption for the literal weighted product gradient. -/
theorem product_caccioppoli_pointwise {η : ProductSpace ι → ℝ} {u : ProductSpace ι → ℂ}
    {p : ProductSpace ι} (hη : DifferentiableAt ℝ η p) (hu : DifferentiableAt ℝ u p) :
    η p ^ 2 * productGradientEnergy u p ≤
      2 * (productGradientPair (fun q => (η q : ℂ) ^ 2 * u q) u p).re +
        4 * productGradientEnergy (fun q => (η q : ℂ)) p * ‖u p‖ ^ 2 := by
  have hd (i : ι) (j : Fin 3) : η p ^ 2 * ‖productPartial u i j p‖ ^ 2 ≤
      2 * (star (productPartial (fun q => (η q : ℂ) ^ 2 * u q) i j p) *
        productPartial u i j p).re +
        4 * ‖productPartial (fun q => (η q : ℂ)) i j p‖ ^ 2 * ‖u p‖ ^ 2 := by
    rw [productPartial_cutoff_square hη hu]
    exact caccioppoli_cutoff_scalar (η p) (u p) (productPartial u i j p)
      (productPartial (fun q => (η q : ℂ)) i j p)
  have hr : (productGradientPair (fun q => (η q : ℂ) ^ 2 * u q) u p).re =
      ∑ i, (p i 2) ^ 2 * ∑ j : Fin 3,
        (star (productPartial (fun q => (η q : ℂ) ^ 2 * u q) i j p) *
          productPartial u i j p).re := by
    simp only [productGradientPair, ← Complex.ofReal_pow, Complex.re_sum,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    _ = ∑ i, (p i 2) ^ 2 * ∑ j : Fin 3, η p ^ 2 * ‖productPartial u i j p‖ ^ 2 := by
      unfold productGradientEnergy
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i, (p i 2) ^ 2 * ∑ j : Fin 3,
        (2 * (star (productPartial (fun q => (η q : ℂ) ^ 2 * u q) i j p) *
          productPartial u i j p).re +
          4 * ‖productPartial (fun q => (η q : ℂ)) i j p‖ ^ 2 * ‖u p‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hd i j)) (sq_nonneg _)
    _ = _ := by
      rw [hr]
      unfold productGradientEnergy
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, mul_add]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
        apply Finset.sum_congr rfl <;> intro j _ <;> ring

end
end ArtinMatthews.SourceHyperbolicGreen
