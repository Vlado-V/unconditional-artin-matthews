module

public import ArtinMatthews.SourceJacquetHaarDilation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite-place modulus is independent of the choice of
additive Haar measure. The integer-ball mass records the conversion
between self-dual Haar and the volume-one Jacquet normalization. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure SourcePhysical Set
open scoped NumberField SourcePhysical Pointwise ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
    (μ : Measure (P.adicCompletion K)) [μ.IsAddHaarMeasure]

theorem sourceLocalAddHaar_map_mul (t : (P.adicCompletion K)ˣ) :
    μ.map (fun x => (t : P.adicCompletion K) * x) =
      (‖((t⁻¹ : (P.adicCompletion K)ˣ) : P.adicCompletion K)‖₊ : ℝ≥0∞) • μ := by
  ext1 s hs
  have hm : Measurable (fun x : P.adicCompletion K => (t : P.adicCompletion K) * x) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hm hs, Measure.smul_apply, smul_eq_mul]
  have he : (fun x : P.adicCompletion K => (t : P.adicCompletion K) * x) ⁻¹' s = t⁻¹ • s := by
    change (fun x : P.adicCompletion K => t • x) ⁻¹' s = t⁻¹ • s
    simpa only [inv_inv] using preimage_smul_inv t⁻¹ s
  rw [he, ← distribHaarChar_mul μ, sourceLocalDistribHaarChar]

theorem sourceLocalAddHaar_setIntegral_dilation {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : (P.adicCompletion K)ˣ) (s : Set (P.adicCompletion K)) (f : P.adicCompletion K → V) :
    (∫ x in (fun x => (t : P.adicCompletion K) * x) '' s, f x ∂μ) =
      ‖(t : P.adicCompletion K)‖ • ∫ x in s, f ((t : P.adicCompletion K) * x) ∂μ := by
  let L := P.adicCompletion K
  let e := MeasurableEquiv.mulLeft₀ ((t⁻¹ : Lˣ) : L) t⁻¹.ne_zero
  have he : μ.map e = (‖(t : L)‖₊ : ℝ≥0∞) • μ := by
    change μ.map (fun x : L => ((t⁻¹ : Lˣ) : L) * x) = _
    rw [sourceLocalAddHaar_map_mul K P μ t⁻¹, inv_inv]
  have hs : e ⁻¹' s = (fun x : L => (t : L) * x) '' s := by
    change (fun x : L => t⁻¹ • x) ⁻¹' s = t • s
    exact preimage_smul_inv t s
  have hf : (fun x => f ((t : L) * e x)) = f := by
    funext x
    apply congrArg f
    change (t : L) * (((t⁻¹ : Lˣ) : L) * x) = x
    rw [Units.val_inv_eq_inv_val, ← mul_assoc, mul_inv_cancel₀ t.ne_zero, one_mul]
  have h := setIntegral_map_equiv (μ := μ) e (fun x => f ((t : L) * x)) s
  rw [he, hs, hf, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal] at h
  exact h.symm

theorem sourceLocalAddHaar_eq_integer_mass_smul_jacquet :
    μ = μ (sourceLocalBall K P 0) • sourceJacquetHaar K P := by
  let ν := sourceJacquetHaar K P
  let : ν.IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  let c := addHaarScalarFactor μ ν
  have he : μ = c • ν := isAddLeftInvariant_eq_smul μ ν
  have hν : ν (sourceLocalBall K P 0) = 1 := by
    rw [sourceLocalBall_zero_eq_integerOpen]
    exact sourceJacquetHaar_integers K P
  have hc : μ (sourceLocalBall K P 0) = (c : ℝ≥0∞) := by
    have h := congrArg (fun m : Measure (P.adicCompletion K) => m (sourceLocalBall K P 0)) he
    change μ (sourceLocalBall K P 0) = (c • ν) (sourceLocalBall K P 0) at h
    rwa [Measure.coe_nnreal_smul_apply, hν, mul_one] at h
  rw [hc]
  exact he

theorem sourceLocalSelfDual_eq_integer_mass_smul_jacquet :
    sourceLocalSelfDual K P = (sourceLocalSelfDual K P) (sourceLocalBall K P 0) • sourceJacquetHaar K P := by
  let : (sourceLocalSelfDual K P).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  exact sourceLocalAddHaar_eq_integer_mass_smul_jacquet K P (sourceLocalSelfDual K P)

end
end ArtinMatthews
