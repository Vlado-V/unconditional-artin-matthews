module

public import ArtinMatthews.VaryingKummerAnalyticGammaIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact positive scaling and diagonal change of variables for Mellin integration.
The scalar argument is extracted from OpenAI PrimePackets/ZeroReflection.lean. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Set Matrix
open scoped Classical BigOperators ENNReal
noncomputable section
lemma lintegral_comp_pos_mul {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ≥0∞) :
    (∫⁻ x, f (c*x)) = ENNReal.ofReal c⁻¹ * ∫⁻ x, f x := by
  have H := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Set.univ) (f := fun x : ℝ => c⁻¹*x) (f' := fun _ => c⁻¹)
    MeasurableSet.univ
    (fun x _ => by simpa using (hasDerivAt_id x).const_mul c⁻¹)
    (fun _ _ _ _ h => mul_left_cancel₀ (inv_ne_zero hc.ne') h)
    (fun x => f (c*x))
  have hi : (fun x : ℝ => c⁻¹*x) '' Set.univ = Set.univ := by
    ext y
    simp only [mem_image, mem_univ, true_and, iff_true]
    exact ⟨c*y, by simp [hc.ne']⟩
  simpa only [hi, Measure.restrict_univ, abs_of_pos (inv_pos.mpr hc),
    ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] using H



theorem lintegral_div_coordinates {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (f : (ι → ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ x : ι → ℝ, f (fun i => x i / m i)) = ENNReal.ofReal (∏ i, m i) * ∫⁻ x, f x := by
  let M : Matrix ι ι ℝ := Matrix.diagonal (fun i => (m i)⁻¹)
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => inv_ne_zero (hm i).ne')
  have he (x : ι → ℝ) : Matrix.toLin' M x = fun i => x i / m i := by
    ext i
    simp [M, Matrix.toLin'_apply, Matrix.mulVec_diagonal, div_eq_mul_inv, mul_comm]
  have hmeas : Measurable (Matrix.toLin' M) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  simp_rw [← he]
  rw [← lintegral_map hf hmeas, Real.map_matrix_volume_pi_eq_smul_volume_pi hdet,
    lintegral_smul_measure]
  congr 2
  rw [Matrix.det_diagonal, Finset.prod_inv_distrib, inv_inv,
    abs_of_pos (Finset.prod_pos (fun i _ => hm i))]

end
end ArtinMatthews.VaryingKummerAnalytic
