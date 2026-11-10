module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Filter MeasureTheory Set
open scoped Topology

/-- A fibrewise real derivative is the pointwise limit of measurable difference quotients. -/
theorem sourceMeasurable_parametric_derivative_zero {X : Type*} [MeasurableSpace X]
    (F : ℝ → X → ℝ) (D : X → ℝ) (hF : ∀ t, Measurable (F t))
    (hD : ∀ x, HasDerivAt (fun t => F t x) (D x) 0) : Measurable D := by
  let u : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hu : Tendsto u atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall (fun n => show 0 < u n by dsimp [u]; positivity)
  let G : ℕ → X → ℝ := fun n x => (u n)⁻¹ * (F (u n) x - F 0 x)
  have hG (n : ℕ) : Measurable (G n) := measurable_const.mul ((hF (u n)).sub (hF 0))
  apply measurable_of_tendsto_metrizable hG
  apply tendsto_pi_nhds.mpr
  intro x
  simpa only [G, Function.comp_def, zero_add, smul_eq_mul] using
    (hD x).tendsto_slope_zero_right.comp hu

end ArtinMatthews
