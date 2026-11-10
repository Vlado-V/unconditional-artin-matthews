module

public import ArtinMatthews.SourceAdditiveMellinDual
public import ArtinMatthews.MarkedMajorFourierWeight
public import Mathlib.Algebra.Ring.IsFormallyReal


set_option backward.privateInPublic true
@[expose] public section

/-! A weighted Fourier pairing estimate in the literal local additive
polynomial, with all real integrals justified. -/

namespace ArtinMatthews
open MeasureTheory Filter
open scoped FourierTransform SchwartzMap BigOperators
noncomputable section

theorem sourceLocalAdditivePolynomial_weight_integrable {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (a : ι → ℂ) {W : ℝ} (hW : 0 < W) {j : ℕ} (hj : 2 ≤ j) :
    Integrable (fun t : ℝ => markedMajorFourierWeight W j t *
      ‖sourceLocalAdditivePolynomial S x a t‖ ^ 2) := by
  let B := ∑ i ∈ S, ‖a i‖
  have hweight : Continuous (markedMajorFourierWeight W j) := by
    unfold markedMajorFourierWeight
    exact ((continuous_const.add (continuous_abs.div_const W)).pow j).inv₀
      (fun t => pow_ne_zero _ (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
        (div_nonneg (abs_nonneg t) hW.le))))
  apply ((markedMajorFourierWeight_integrable hW hj).mul_const (B ^ 2)).mono'
  · exact (hweight.mul ((sourceLocalAdditivePolynomial_contDiff S x a).continuous.norm.pow 2)).aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    have hw := markedMajorFourierWeight_nonneg hW j t
    rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (sourceLocalAdditivePolynomial_norm_le S x a t) 2) hw

private theorem weighted_product_le (u v : ℝ) {w D : ℝ} (hw : 0 < w) (hD : 0 < D) :
    u * v ≤ (w * u ^ 2) / (2 * D) + (D / 2) * (w⁻¹ * v ^ 2) := by
  calc
    _ ≤ ((w * u) ^ 2 + (D * v) ^ 2) / (2 * D * w) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith [sq_nonneg (w * u - D * v)])
    _ = _ := by field_simp [hw.ne', hD.ne']

theorem sourceMellin_weighted_pairing_le {ι : Type*} (S : Finset ι) (x : ι → ℝ) (a : ι → ℂ)
    (G : 𝓢(ℝ, ℂ)) {W D : ℝ} (hW : 0 < W) (hD : 0 < D) {j : ℕ} (hj : 2 ≤ j) :
    ‖∫ t : ℝ, sourceLocalAdditivePolynomial S x a t * (𝓕 G) t‖ ≤
      (∫ t : ℝ, (1 + |t| / W) ^ j * ‖(𝓕 G) t‖ ^ 2) / (2 * D) +
        (D / 2) * ∫ t : ℝ, markedMajorFourierWeight W j t *
          ‖sourceLocalAdditivePolynomial S x a t‖ ^ 2 := by
  let F := sourceLocalAdditivePolynomial S x a
  let Ghat : 𝓢(ℝ, ℂ) := 𝓕 G
  let p (t : ℝ) := (1 + |t| / W) ^ j * ‖Ghat t‖ ^ 2
  let m (t : ℝ) := markedMajorFourierWeight W j t * ‖F t‖ ^ 2
  let B := ∑ i ∈ S, ‖a i‖
  have hp : Integrable p := (sourceMellinSchwartz_weighted_fourier_energy G hW j).1
  have hm : Integrable m := sourceLocalAdditivePolynomial_weight_integrable S x a hW hj
  have hF : Continuous F := (sourceLocalAdditivePolynomial_contDiff S x a).continuous
  have hprod : Integrable (fun t => F t * Ghat t) := by
    apply (Ghat.integrable.norm.const_mul B).mono' (hF.mul Ghat.continuous).aestronglyMeasurable
    exact Eventually.of_forall fun t => by
      change ‖F t * Ghat t‖ ≤ B * ‖Ghat t‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (sourceLocalAdditivePolynomial_norm_le S x a t) (norm_nonneg _)
  calc
    _ ≤ ∫ t : ℝ, ‖F t * Ghat t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, p t / (2 * D) + (D / 2) * m t := by
      apply integral_mono hprod.norm ((hp.div_const _).add (hm.const_mul _))
      intro t
      change ‖F t * Ghat t‖ ≤ p t / (2 * D) + (D / 2) * m t
      rw [norm_mul, mul_comm ‖F t‖]
      exact weighted_product_le ‖Ghat t‖ ‖F t‖ (by positivity : 0 < (1 + |t| / W) ^ j) hD
    _ = _ := by
      rw [integral_add (hp.div_const _) (hm.const_mul _), integral_div, integral_const_mul]

end
end ArtinMatthews
