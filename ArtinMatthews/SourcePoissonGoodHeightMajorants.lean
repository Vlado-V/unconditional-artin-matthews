module

public import ArtinMatthews.SourceContinuedPoissonMagnitude
public import ArtinMatthews.SourceGaussianHeightDecay


set_option backward.privateInPublic true
@[expose] public section

/-! Positive height majorants for the two finite horizontal sides and
the discarded right tail. The translation in the actual Gaussian gives
arbitrary power decay at the cutoff height. -/
namespace ArtinMatthews.SourcePhysical
open MeasureTheory VaryingKummerAnalytic
noncomputable section

def sourcePoissonHeightPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  (1+|x|)^n*Real.exp (-(x^2))

def sourcePoissonHeightMoment (n : ℕ) (p : SourcePoissonHeights) : ℝ :=
  (sourceContourHeightWeight p.1.1*sourceContourHeightWeight p.1.2)*
    sourcePoissonHeightPolynomial n (p.2+p.1.2)

theorem sourcePoissonHeightPolynomial_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ sourcePoissonHeightPolynomial n x := by
  unfold sourcePoissonHeightPolynomial
  positivity

theorem sourcePoissonHeightMoment_nonneg (n : ℕ) (p : SourcePoissonHeights) :
    0 ≤ sourcePoissonHeightMoment n p :=
  mul_nonneg (mul_nonneg (sourceContourHeightWeight_nonneg _) (sourceContourHeightWeight_nonneg _))
    (sourcePoissonHeightPolynomial_nonneg _ _)

theorem sourcePoissonHeightMoment_integrable (n : ℕ) :
    Integrable (sourcePoissonHeightMoment n) sourcePoissonHeightMeasure := by
  have hn : Integrable (sourcePoissonHeightPolynomial n) := source_gaussian_polynomial_integrable n
  have h := (sourceContourHeightWeight_integrable.mul_prod sourceContourHeightWeight_integrable).mul_prod hn
  exact (sourceLogRadial_shear_measurePreserving ((volume : Measure ℝ).prod volume)
    (Prod.snd : ℝ × ℝ → ℝ) measurable_snd).integrable_comp_of_integrable h

theorem sourcePoissonHeightMoment_horizontal_integrable (n : ℕ) (x : ℝ) :
    Integrable (fun wt : ℝ × ℝ => sourcePoissonHeightMoment n (wt,x)) ((volume : Measure ℝ).prod volume) := by
  have hn : Integrable (sourcePoissonHeightPolynomial n) := source_gaussian_polynomial_integrable n
  have ht : Integrable (fun t : ℝ => sourceContourHeightWeight t*sourcePoissonHeightPolynomial n (x+t)) := by
    have hg := hn.comp_add_left x
    apply hg.mono' (sourceContourHeightWeight_integrable.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    filter_upwards with t
    change ‖sourceContourHeightWeight t*sourcePoissonHeightPolynomial n (x+t)‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (sourceContourHeightWeight_nonneg _) (sourcePoissonHeightPolynomial_nonneg _ _))]
    exact mul_le_of_le_one_left (sourcePoissonHeightPolynomial_nonneg _ _) (sourceContourHeightWeight_le_one t)
  have h := sourceContourHeightWeight_integrable.mul_prod ht
  simpa only [sourcePoissonHeightMoment, mul_assoc] using h

theorem sourcePoissonHeightMoment_horizontal_mass (n : ℕ) (x : ℝ) :
    (∫ wt : ℝ × ℝ, sourcePoissonHeightMoment n (wt,x) ∂(volume : Measure ℝ).prod volume) ≤
      (∫ y : ℝ, sourceContourHeightWeight y)*sourceGaussianPolynomialMoment n := by
  have hn : Integrable (sourcePoissonHeightPolynomial n) := source_gaussian_polynomial_integrable n
  have hg := hn.comp_add_left x
  have ht : Integrable (fun t : ℝ => sourceContourHeightWeight t*sourcePoissonHeightPolynomial n (x+t)) := by
    apply hg.mono' (sourceContourHeightWeight_integrable.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    filter_upwards with t
    change ‖sourceContourHeightWeight t*sourcePoissonHeightPolynomial n (x+t)‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (sourceContourHeightWeight_nonneg _) (sourcePoissonHeightPolynomial_nonneg _ _))]
    exact mul_le_of_le_one_left (sourcePoissonHeightPolynomial_nonneg _ _) (sourceContourHeightWeight_le_one t)
  let g (t : ℝ) := sourceContourHeightWeight t*sourcePoissonHeightPolynomial n (x+t)
  have h : (∫ wt : ℝ × ℝ, sourcePoissonHeightMoment n (wt,x) ∂(volume : Measure ℝ).prod volume) =
      (∫ y : ℝ, sourceContourHeightWeight y)*(∫ t : ℝ, g t) := by
    simp only [sourcePoissonHeightMoment, mul_assoc]
    exact integral_prod_mul sourceContourHeightWeight g
  rw [h]
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg sourceContourHeightWeight_nonneg)
  calc
    _ ≤ ∫ t : ℝ, sourcePoissonHeightPolynomial n (x+t) :=
      integral_mono ht hg (fun t => mul_le_of_le_one_left (sourcePoissonHeightPolynomial_nonneg _ _)
        (sourceContourHeightWeight_le_one _))
    _ = _ := integral_add_left_eq_self (sourcePoissonHeightPolynomial n) x

theorem sourcePoissonHeightWeight_of_one_add_abs_sq (t : ℝ) :
    ((1+|t|)^2)⁻¹ ≤ sourceContourHeightWeight t := by
  rw [sourceContourHeightWeight, ← one_div, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_abs t, abs_nonneg t])

theorem sourcePoissonHeight_decay_pointwise (n : ℕ) (y t x T : ℝ) (hT : 0 ≤ T) (hx : T ≤ |x|) :
    sourceContourHeightWeight y*(Real.exp (-((x+t)^2))/(1+|t|)^(n+2)) ≤
      ((1+T)^n)⁻¹*sourcePoissonHeightMoment n ((y,t),x) := by
  have h₁ := source_gaussian_convolution_pointwise n x t
  have h₂ := sourcePoissonHeightWeight_of_one_add_abs_sq t
  have h₃ : ((1+|x|)^n)⁻¹ ≤ ((1+T)^n)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) _)
  have hG := sourcePoissonHeightPolynomial_nonneg n (x+t)
  calc
    _ = sourceContourHeightWeight y*
        ((Real.exp (-((x+t)^2))/(1+|t|)^n)*((1+|t|)^2)⁻¹) := by
      rw [pow_add, div_eq_mul_inv, mul_inv, div_eq_mul_inv, mul_assoc]
    _ ≤ sourceContourHeightWeight y*
        ((sourcePoissonHeightPolynomial n (x+t)/(1+|x|)^n)*sourceContourHeightWeight t) :=
      mul_le_mul_of_nonneg_left (mul_le_mul h₁ h₂ (by positivity) (div_nonneg hG (by positivity)))
        (sourceContourHeightWeight_nonneg _)
    _ = ((1+|x|)^n)⁻¹*sourcePoissonHeightMoment n ((y,t),x) := by
      simp only [sourcePoissonHeightMoment, div_eq_mul_inv]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h₃ (sourcePoissonHeightMoment_nonneg _ _)

theorem sourcePoissonHeight_cutoffPower_le (n : ℕ) {U r : ℝ} (hU : 0 < U) :
    ((1+U^r)^n)⁻¹ ≤ U^(-r*(n : ℝ)) := by
  have h := one_div_le_one_div_of_le (pow_pos (Real.rpow_pos_of_pos hU r) n)
    (pow_le_pow_left₀ (Real.rpow_nonneg hU.le r) (le_add_of_nonneg_left zero_le_one) n)
  rw [one_div, one_div, ← Real.rpow_mul_natCast hU.le, ← Real.rpow_neg hU.le] at h
  simpa only [neg_mul] using h

end
end ArtinMatthews.SourcePhysical
