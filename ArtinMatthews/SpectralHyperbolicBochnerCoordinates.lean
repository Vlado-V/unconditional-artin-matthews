module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure


set_option backward.privateInPublic true
@[expose] public section

/-! Bochner coordinate integration for the actual invariant H² measure.
The vector-valued version is used for weak derivative pairings. -/

noncomputable section
open MeasureTheory Set

namespace ArtinMatthews

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem upperHalfPlane_integral_coordinates_smul (G : ℝ × ℝ → E) :
    (∫ z : UpperHalfPlane, G (z.re,z.im)) =
      ∫ p in {p : ℝ × ℝ | 0 < p.2}, (p.2^2)⁻¹ • G p := by
  have hcoe : MeasurePreserving UpperHalfPlane.coe
      (volume.comap UpperHalfPlane.coe)
      (volume.restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe,
      UpperHalfPlane.measurableEmbedding_coe.map_comap volume⟩
  let S : Set (ℝ × ℝ) := {p | 0 < p.2}
  have hprod : MeasurePreserving Complex.measurableEquivRealProd
      (volume.restrict (Complex.measurableEquivRealProd ⁻¹' S))
      (volume.restrict S) := by
    refine ⟨Complex.measurableEquivRealProd.measurable, ?_⟩
    rw [← Complex.measurableEquivRealProd.restrict_map,
      Complex.volume_preserving_equiv_real_prod.map_eq]
  rw [UpperHalfPlane.volume_def,
    integral_withDensity_eq_integral_smul (by fun_prop)]
  calc
    _ = ∫ z : UpperHalfPlane, (z.im^2)⁻¹ • G (z.re,z.im)
        ∂volume.comap UpperHalfPlane.coe := by
      apply integral_congr_ae
      filter_upwards with z
      rw [NNReal.smul_def, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
        NNReal.coe_mk, one_div, inv_pow]
    _ = ∫ z : ℂ in range UpperHalfPlane.coe, (z.im^2)⁻¹ • G (z.re,z.im) :=
      hcoe.integral_comp UpperHalfPlane.measurableEmbedding_coe
        (fun z : ℂ => (z.im^2)⁻¹ • G (z.re,z.im))
    _ = ∫ p in S, (p.2^2)⁻¹ • G p := by
      convert hprod.integral_comp' (fun p => (p.2^2)⁻¹ • G p) using 1
      rw [UpperHalfPlane.range_coe]
      rfl

theorem upperHalfPlane_setIntegral_coordinates_smul (G : ℝ × ℝ → E)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hpositive : S ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    (∫ z : UpperHalfPlane in {z | (z.re,z.im) ∈ S}, G (z.re,z.im)) =
      ∫ p in S, (p.2^2)⁻¹ • G p := by
  classical
  have h := upperHalfPlane_integral_coordinates_smul (S.indicator G)
  have hleft : (fun z : UpperHalfPlane => S.indicator G (z.re,z.im)) =
      {z : UpperHalfPlane | (z.re,z.im) ∈ S}.indicator
        (fun z => G (z.re,z.im)) := rfl
  have hright : (fun p : ℝ × ℝ => (p.2^2)⁻¹ • S.indicator G p) =
      S.indicator (fun p => (p.2^2)⁻¹ • G p) := by
    funext p
    by_cases hp : p ∈ S <;> simp [hp]
  have hpre : MeasurableSet {z : UpperHalfPlane | (z.re,z.im) ∈ S} :=
    hS.preimage (by fun_prop)
  rw [hleft, integral_indicator hpre, hright, integral_indicator hS,
    Measure.restrict_restrict_of_subset hpositive] at h
  exact h

/-- Multiplication by height squared cancels the invariant density, for
an actual function supported in the positive half-plane. -/
theorem upperHalfPlane_integral_height_sq (G : ℝ × ℝ → E)
    (hG : ∀ p : ℝ × ℝ, ¬ 0 < p.2 → G p = 0) :
    (∫ z : UpperHalfPlane, z.im^2 • G (z.re,z.im)) = ∫ p, G p := by
  rw [upperHalfPlane_integral_coordinates_smul (fun p => p.2^2 • G p)]
  calc
    _ = ∫ p in {p : ℝ × ℝ | 0 < p.2}, G p := by
      apply setIntegral_congr_fun (by measurability)
      intro p hp
      change (p.2^2)⁻¹ • (p.2^2 • G p) = G p
      rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hp)), one_smul]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero hG

end ArtinMatthews
