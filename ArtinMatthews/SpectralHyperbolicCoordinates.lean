module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure


set_option backward.privateInPublic true
@[expose] public section

/-! Coordinate integration for the actual invariant measure on H². -/

noncomputable section
open MeasureTheory Set

namespace ArtinMatthews

/-- The existing invariant measure on the upper half-plane has exactly the
coordinate density used by the cusp-energy argument. -/
theorem upperHalfPlane_integral_coordinates (G : ℝ × ℝ → ℝ) :
    (∫ z : UpperHalfPlane, G (z.re, z.im)) =
      ∫ p in {p : ℝ × ℝ | 0 < p.2}, G p / p.2 ^ 2 := by
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
    _ = ∫ z : UpperHalfPlane, G (z.re, z.im) / z.im ^ 2
        ∂volume.comap UpperHalfPlane.coe := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [NNReal.smul_def, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
        NNReal.coe_mk, smul_eq_mul]
      ring
    _ = ∫ z : ℂ in range UpperHalfPlane.coe, G (z.re, z.im) / z.im ^ 2 :=
      hcoe.integral_comp UpperHalfPlane.measurableEmbedding_coe
        (fun z : ℂ => G (z.re, z.im) / z.im ^ 2)
    _ = ∫ p in S, G p / p.2 ^ 2 := by
      convert hprod.integral_comp' (fun p => G p / p.2 ^ 2) using 1
      rw [UpperHalfPlane.range_coe]
      rfl

/-- Restriction to a measurable coordinate region lying above the real axis. -/
theorem upperHalfPlane_setIntegral_coordinates (G : ℝ × ℝ → ℝ)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hpositive : S ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    (∫ z : UpperHalfPlane in {z | (z.re, z.im) ∈ S}, G (z.re, z.im)) =
      ∫ p in S, G p / p.2 ^ 2 := by
  classical
  have h := upperHalfPlane_integral_coordinates (S.indicator G)
  have hleft : (fun z : UpperHalfPlane => S.indicator G (z.re, z.im)) =
      {z : UpperHalfPlane | (z.re, z.im) ∈ S}.indicator
        (fun z => G (z.re, z.im)) := by
    funext z
    by_cases hz : (z.re, z.im) ∈ S <;> simp [hz]
  have hright : (fun p : ℝ × ℝ => S.indicator G p / p.2 ^ 2) =
      S.indicator (fun p => G p / p.2 ^ 2) := by
    funext p
    by_cases hp : p ∈ S <;> simp [hp]
  have hpre : MeasurableSet {z : UpperHalfPlane | (z.re, z.im) ∈ S} :=
    hS.preimage (by fun_prop)
  rw [hleft, integral_indicator hpre, hright,
    integral_indicator hS, Measure.restrict_restrict_of_subset hpositive] at h
  exact h

end ArtinMatthews
