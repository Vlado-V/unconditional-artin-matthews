module

public import ArtinMatthews.StandardLocalBallDilation
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar


set_option backward.privateInPublic true
@[expose] public section

/-! The modulus of an actual finite-place dilation, with the absolute
value normalized by the residue cardinality. -/

namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory Set
open scoped NumberField ENNReal NNReal Pointwise
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

theorem sourceLocalBall_smul (n : ℤ) (t : (P.adicCompletion K)ˣ) :
    t • sourceLocalBall K P n =
      sourceLocalBall K P (n + WithZero.log (sourceLocalValuation K P (t : P.adicCompletion K))) := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem]
  change (((t⁻¹ : (P.adicCompletion K)ˣ) : P.adicCompletion K) * x ∈
    sourceLocalBall K P n) ↔ _
  rw [Units.val_inv_eq_inv_val, ← div_eq_inv_mul]
  exact sourceLocalBall_div_mem K P n t x

theorem sourceLocalDistribHaarChar (t : (P.adicCompletion K)ˣ) :
    distribHaarChar (P.adicCompletion K) t = ‖(t : P.adicCompletion K)‖₊ := by
  let μ := sourceLocalSelfDual K P
  let : μ.IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  have h := congrArg ENNReal.toReal (distribHaarChar_mul μ t (sourceLocalBall K P 0))
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, sourceLocalBall_smul] at h
  apply NNReal.coe_injective
  exact mul_right_cancel₀ (sourceLocalBall_volume_pos K P 0).ne'
    (h.trans (sourceLocalBall_dilation_volume K P μ 0 t))

theorem sourceLocalSelfDual_map_mul (t : (P.adicCompletion K)ˣ) :
    (sourceLocalSelfDual K P).map (fun x => (t : P.adicCompletion K) * x) =
      (‖((t⁻¹ : (P.adicCompletion K)ˣ) : P.adicCompletion K)‖₊ : ℝ≥0∞) •
        sourceLocalSelfDual K P := by
  let μ := sourceLocalSelfDual K P
  let : μ.IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  ext1 s hs
  have hm : Measurable (fun x : P.adicCompletion K => (t : P.adicCompletion K) * x) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hm hs, Measure.smul_apply, smul_eq_mul]
  have he : (fun x : P.adicCompletion K => (t : P.adicCompletion K) * x) ⁻¹' s = t⁻¹ • s := by
    change (fun x : P.adicCompletion K => t • x) ⁻¹' s = t⁻¹ • s
    simpa only [inv_inv] using preimage_smul_inv t⁻¹ s
  rw [he, ← distribHaarChar_mul μ, sourceLocalDistribHaarChar]

end
end ArtinMatthews.SourcePhysical
