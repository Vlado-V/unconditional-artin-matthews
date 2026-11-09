module

public import ArtinMatthews.SourceJacquetIntegrabilityDilation
public import ArtinMatthews.SourceJacquetAdditiveTranslation


set_option backward.privateInPublic true
@[expose] public section

/-! Whole-field affine changes of variable for the actual local
additive Haar measure. The finite-place modulus and integrability
are retained explicitly. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical Set
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "μ₀" => sourceJacquetHaar K P

theorem sourceLocalIntegral_translate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u : L) (f : L → V) : (∫ x, f (x + u) ∂μ₀) = ∫ x, f x ∂μ₀ := by
  let : (sourceJacquetHaar K P).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  exact integral_add_right_eq_self f u

theorem sourceLocalIntegrable_translate_iff {V : Type*} [NormedAddCommGroup V]
    (u : L) (f : L → V) : Integrable (fun x => f (x + u)) μ₀ ↔ Integrable f μ₀ := by
  let : (sourceJacquetHaar K P).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  let e := MeasurableEquiv.addRight u
  have he : MeasurePreserving e μ₀ μ₀ := measurePreserving_add_right μ₀ u
  exact he.integrable_comp_emb e.measurableEmbedding

theorem sourceLocalIntegral_mul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hP : P ∉ traceBadPlaces K) (y : Lˣ) (f : L → V) :
    (∫ x, f x ∂μ₀) = ‖(y : L)‖ • ∫ x, f ((y : L) * x) ∂μ₀ := by
  have hs : (fun x : L => (y : L) * x) '' (univ : Set L) = univ :=
    Set.image_univ_of_surjective (mul_left_surjective₀ y.ne_zero)
  have h := sourceJacquetSetIntegral_dilation K P hP y univ f
  simpa only [hs, setIntegral_univ] using h

theorem sourceLocalIntegrable_mul_iff {V : Type*} [NormedAddCommGroup V]
    (hP : P ∉ traceBadPlaces K) (y : Lˣ) (f : L → V) :
    Integrable (fun x => f ((y : L) * x)) μ₀ ↔ Integrable f μ₀ := by
  have hs : (fun x : L => (y : L) * x) '' (univ : Set L) = univ :=
    Set.image_univ_of_surjective (mul_left_surjective₀ y.ne_zero)
  have h := sourceJacquetIntegrableOn_dilation_iff K P hP y univ f
  simpa only [hs, integrableOn_univ] using h.symm

theorem sourceLocalIntegral_div {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hP : P ∉ traceBadPlaces K) (y : Lˣ) (f : L → V) :
    (∫ x, f (x / (y : L)) ∂μ₀) = ‖(y : L)‖ • ∫ x, f x ∂μ₀ := by
  have h := sourceLocalIntegral_mul K P hP y (fun x => f (x / (y : L)))
  have he : (fun x : L => f ((y : L) * x / (y : L))) = f := by
    funext x
    rw [mul_div_cancel_left₀ x y.ne_zero]
  rwa [he] at h

theorem sourceLocalIntegrable_div_iff {V : Type*} [NormedAddCommGroup V]
    (hP : P ∉ traceBadPlaces K) (y : Lˣ) (f : L → V) :
    Integrable (fun x => f (x / (y : L))) μ₀ ↔ Integrable f μ₀ := by
  have he : (fun x : L => f (((y⁻¹ : Lˣ) : L) * x)) = fun x => f (x / (y : L)) := by
    funext x
    rw [Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm]
  rw [← he]
  exact sourceLocalIntegrable_mul_iff K P hP y⁻¹ f

theorem sourceLocalIntegral_affine {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hP : P ∉ traceBadPlaces K) (u : L) (y : Lˣ) (f : L → V) :
    (∫ x, f ((x + u) / (y : L)) ∂μ₀) = ‖(y : L)‖ • ∫ x, f x ∂μ₀ := by
  rw [sourceLocalIntegral_translate K P u (fun x => f (x / (y : L))),
    sourceLocalIntegral_div K P hP y f]

theorem sourceLocalIntegrable_affine_iff {V : Type*} [NormedAddCommGroup V]
    (hP : P ∉ traceBadPlaces K) (u : L) (y : Lˣ) (f : L → V) :
    Integrable (fun x => f ((x + u) / (y : L))) μ₀ ↔ Integrable f μ₀ := by
  rw [sourceLocalIntegrable_translate_iff K P u (fun x => f (x / (y : L))),
    sourceLocalIntegrable_div_iff K P hP y f]

end
end ArtinMatthews
