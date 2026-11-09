module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Group.Circle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory Set
open scoped ENNReal Real
noncomputable section

private instance : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- Unnormalized angle Haar measure, of total mass 2π. -/
def sourceCircleHaar : Measure Circle :=
  Measure.map AddCircle.homeomorphCircle' (volume : Measure (AddCircle (2 * π)))

theorem sourceCircleHaar_univ : sourceCircleHaar univ = ENNReal.ofReal (2 * π) := by
  rw [sourceCircleHaar, Measure.map_apply AddCircle.homeomorphCircle'.continuous.measurable
    MeasurableSet.univ, preimage_univ]
  exact AddCircle.measure_univ (2 * π)

theorem sourceCircleHaar_eq_map_exp :
    sourceCircleHaar = Measure.map (fun t : ℝ => Circle.exp t) (volume.restrict (Ioo (-π) π)) := by
  have hm := AddCircle.measurePreserving_mk (T := 2 * π) (-π)
  have hc : -π + 2 * π = π := by ring
  rw [hc] at hm
  rw [restrict_Ioo_eq_restrict_Ioc, sourceCircleHaar, ← hm.map_eq,
    Measure.map_map AddCircle.homeomorphCircle'.continuous.measurable hm.measurable]
  rfl

theorem sourceCircleHaar_isHaar : sourceCircleHaar.IsHaarMeasure := by
  let : MeasurableSpace (Multiplicative (AddCircle (2 * π))) :=
    inferInstanceAs (MeasurableSpace (AddCircle (2 * π)))
  have : BorelSpace (Multiplicative (AddCircle (2 * π))) :=
    inferInstanceAs (BorelSpace (AddCircle (2 * π)))
  let μ : Measure (Multiplicative (AddCircle (2 * π))) :=
    (volume : Measure (AddCircle (2 * π)))
  have : μ.IsHaarMeasure :=
    { lt_top_of_isCompact := fun s hs => hs.measure_lt_top (μ := (volume : Measure (AddCircle (2 * π))))
      map_mul_left_eq_self := fun x =>
        map_add_left_eq_self (volume : Measure (AddCircle (2 * π))) x.toAdd
      open_pos := fun s hs hn => hs.measure_ne_zero (volume : Measure (AddCircle (2 * π))) hn }
  let e : Multiplicative (AddCircle (2 * π)) ≃* Circle :=
    { toEquiv := AddCircle.homeomorphCircle'.toEquiv
      map_mul' := Real.Angle.toCircle_add }
  exact e.isHaarMeasure_map μ
    AddCircle.homeomorphCircle'.continuous AddCircle.homeomorphCircle'.symm.continuous

theorem sourceCircleHaar_lintegral (f : Circle → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂sourceCircleHaar) = ∫⁻ θ in Ioo (-π) π, f (Circle.exp θ) := by
  rw [sourceCircleHaar_eq_map_exp, lintegral_map hf Circle.exp.continuous.measurable]

end
end ArtinMatthews.SourcePhysical
