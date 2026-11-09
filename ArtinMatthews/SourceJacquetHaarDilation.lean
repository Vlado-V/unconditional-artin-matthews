module

public import ArtinMatthews.SourceJacquetHaar
public import ArtinMatthews.SourceLocalAdditiveModulus
public import Mathlib.MeasureTheory.Group.MeasurableEquiv


set_option backward.privateInPublic true
@[expose] public section

/-! The volume-one Haar of the literal Jacquet calculation is the
actual standard self-dual Haar at an exterior place. Dilation of a
set integral has the exact normalized finite-place modulus. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical Set
open scoped NumberField SourcePhysical Pointwise ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

theorem sourceJacquetHaar_eq_selfDual (hP : P ∉ traceBadPlaces K) :
    sourceJacquetHaar K P = sourceLocalSelfDual K P := by
  let : (sourceJacquetHaar K P).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  refine sourceLocalSelfDual_eq_of_good_volume K P _ hP ?_
  rw [sourceLocalBall_zero_eq_integerOpen]
  exact sourceJacquetHaar_integers K P

theorem sourceJacquetSetIntegral_dilation {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hP : P ∉ traceBadPlaces K) (t : (P.adicCompletion K)ˣ) (s : Set (P.adicCompletion K))
    (f : P.adicCompletion K → V) :
    (∫ x in (fun x => (t : P.adicCompletion K) * x) '' s, f x ∂(sourceJacquetHaar K P)) =
      ‖(t : P.adicCompletion K)‖ •
        ∫ x in s, f ((t : P.adicCompletion K) * x) ∂(sourceJacquetHaar K P) := by
  let L := P.adicCompletion K
  let μ := sourceJacquetHaar K P
  let e := MeasurableEquiv.mulLeft₀ ((t⁻¹ : Lˣ) : L) t⁻¹.ne_zero
  have he : μ.map e = (‖(t : L)‖₊ : ℝ≥0∞) • μ := by
    change μ.map (fun x : L => ((t⁻¹ : Lˣ) : L) * x) = _
    rw [show μ = sourceLocalSelfDual K P from sourceJacquetHaar_eq_selfDual K P hP,
      sourceLocalSelfDual_map_mul K P t⁻¹, inv_inv]
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

end
end ArtinMatthews
