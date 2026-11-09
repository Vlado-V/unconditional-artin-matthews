module

public import ArtinMatthews.SpectralKSquareMomentBand


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit mass for the actual K kernel in a compact dyadic band
under the model-cusp measure dx/x. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectralKLPhysical_setIntegral_div (F : ℝ → ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) (hPos : S ⊆ Ioi 0) :
    (∫ x in S, F x ∂spectralKLPhysicalMeasure) = ∫ x in S, F x/x := by
  rw [← integral_indicator hS,spectralKLPhysicalMeasure,
    spectralKLPositiveWeightMeasure_integral _ _ (by fun_prop) (fun x hx => inv_nonneg.mpr hx.le)]
  have he : (fun x => x⁻¹*S.indicator F x) = S.indicator (fun x => F x/x) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx,div_eq_inv_mul]
    · simp only [Set.indicator_of_notMem hx,mul_zero]
  rw [he,integral_indicator hS,Measure.restrict_restrict_of_subset hPos]

theorem spectralKSquareBand_div_integrable (t : ℝ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (spectralKLRealKernel t x)^2/x) (Ioc a b) := by
  have hF : IntegrableOn (fun x : ℝ => (spectralKLRealKernel t x)^2) (Ioc a b) := by
    have h := (spectralKSquareMoment_integrable 0 t).mono_set
      (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha.le) : Ioc a b ⊆ Ioi 0)
    simpa only [mul_zero,pow_zero,one_mul] using h
  have hInv : ContinuousOn (fun x : ℝ => x⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun x hx => (ha.trans_le hx.1).ne')
  simpa only [div_eq_inv_mul] using
    hF.continuousOn_mul_of_subset hInv isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self

theorem spectralKSquareBand_weighted_lower (t : ℝ) :
    (spectralKSquareMoment 0 t/108)/(spectralKSquareBandUpper t) ≤
      ∫ x in Ioc (spectralKSquareBandLower t) (spectralKSquareBandUpper t),
        (spectralKLRealKernel t x)^2/x := by
  let a := spectralKSquareBandLower t
  let b := spectralKSquareBandUpper t
  let F (x : ℝ) := (spectralKLRealKernel t x)^2
  have ha : 0 < a := spectralKSquareBandLower_pos t
  have hb : 0 < b := spectralKSquareBandUpper_pos t
  have hF : IntegrableOn F (Ioc a b) := by
    have h := (spectralKSquareMoment_integrable 0 t).mono_set
      (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha.le) : Ioc a b ⊆ Ioi 0)
    simpa only [F,mul_zero,pow_zero,one_mul] using h
  apply (div_le_iff₀ hb).mpr
  calc
    _ ≤ ∫ x in Ioc a b, F x := spectralKSquareBand_lower t
    _ ≤ ∫ x in Ioc a b, b*(F x/x) := by
      apply setIntegral_mono_on hF ((spectralKSquareBand_div_integrable t ha).const_mul b) measurableSet_Ioc
      intro x hx
      have hx0 := ha.trans hx.1
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hx0).mpr
      rw [mul_comm b]
      exact mul_le_mul_of_nonneg_left hx.2 (sq_nonneg _)
    _ = _ := by rw [integral_const_mul,mul_comm]

theorem spectralKSquareBandLower_dyadic (t : ℝ) :
    (1+|t|)/8 ≤ spectralKSquareBandLower t := by
  unfold spectralKSquareBandLower
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  nlinarith [sq_nonneg (|t|-1),sq_abs t,sq_nonneg t]

theorem spectralKSquareBandUpper_dyadic (t : ℝ) :
    spectralKSquareBandUpper t ≤ 3*(1+|t|) := by
  unfold spectralKSquareBandUpper
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  nlinarith [sq_abs t,sq_nonneg t,abs_nonneg t]

theorem spectralKSquareDyadicBand_physical_lower (t T : ℝ) (hT : 0 < T)
    (ht₁ : T ≤ 1+|t|) (ht₂ : 1+|t| ≤ 2*T) :
    Real.pi^2/(2592*T*Real.cosh (Real.pi*t)) ≤
      ∫ x in Ioc (T/8) (6*T), (spectralKLRealKernel t x)^2 ∂spectralKLPhysicalMeasure := by
  let a := spectralKSquareBandLower t
  let b := spectralKSquareBandUpper t
  let F (x : ℝ) := (spectralKLRealKernel t x)^2
  have ha₀ : 0 < T/8 := by positivity
  have hb : 0 < b := spectralKSquareBandUpper_pos t
  have haT : T/8 ≤ a :=
    (div_le_div_of_nonneg_right ht₁ (by norm_num)).trans (spectralKSquareBandLower_dyadic t)
  have hbT : b ≤ 6*T := by
    have h := (spectralKSquareBandUpper_dyadic t).trans (mul_le_mul_of_nonneg_left ht₂ (by norm_num : (0 : ℝ) ≤ 3))
    linarith
  have hPos : Ioc (T/8) (6*T) ⊆ Ioi (0 : ℝ) :=
    Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha₀.le)
  rw [spectralKLPhysical_setIntegral_div _ measurableSet_Ioc hPos]
  have hc := Real.cosh_pos (Real.pi*t)
  have hd : 4*Real.cosh (Real.pi*t)*108*b ≤ 2592*T*Real.cosh (Real.pi*t) := by
    calc
      _ = (432*Real.cosh (Real.pi*t))*b := by ring
      _ ≤ (432*Real.cosh (Real.pi*t))*(6*T) := mul_le_mul_of_nonneg_left hbT (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (spectralKSquareMoment 0 t/108)/b := by
      rw [spectralKSquareMoment_zero,div_div,div_div]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by simpa only [mul_assoc] using hd)
    _ ≤ ∫ x in Ioc a b, F x/x := spectralKSquareBand_weighted_lower t
    _ ≤ _ := by
      apply setIntegral_mono_set (spectralKSquareBand_div_integrable t ha₀)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact div_nonneg (sq_nonneg _) (ha₀.trans hx.1).le
      · exact Eventually.of_forall (fun x hx => ⟨haT.trans_lt hx.1,hx.2.trans hbT⟩)

end ArtinMatthews
