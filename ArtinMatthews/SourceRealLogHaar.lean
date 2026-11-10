module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory
noncomputable section

scoped instance sourceMultiplicativeRealMeasurableSpace : MeasurableSpace (Multiplicative ℝ) :=
  inferInstanceAs (MeasurableSpace ℝ)

scoped instance sourceMultiplicativeRealBorelSpace : BorelSpace (Multiplicative ℝ) :=
  inferInstanceAs (BorelSpace ℝ)

/-- Lebesgue measure in the logarithm is multiplicative Haar in the positive radial parameter. -/
def sourceRealLogHaar : Measure (Multiplicative ℝ) := (volume : Measure ℝ)

instance sourceRealLogHaar_sigmaFinite : SigmaFinite sourceRealLogHaar :=
  inferInstanceAs (SigmaFinite (volume : Measure ℝ))

instance sourceRealLogHaar_isHaar : sourceRealLogHaar.IsHaarMeasure where
  lt_top_of_isCompact _ hs := hs.measure_lt_top (μ := (volume : Measure ℝ))
  map_mul_left_eq_self t := map_add_left_eq_self (volume : Measure ℝ) t.toAdd
  open_pos _ hs hn := hs.measure_ne_zero (volume : Measure ℝ) hn

end
end ArtinMatthews.SourcePhysical
