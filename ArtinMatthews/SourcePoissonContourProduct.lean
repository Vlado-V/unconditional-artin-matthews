module

public import ArtinMatthews.SourcePoissonMellinHeight


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory
noncomputable section

theorem sourcePoissonVertical_add_sub_one (a c u v : ℝ) :
    sourcePoissonVertical a u + sourcePoissonVertical c v - 1 =
      sourcePoissonVertical (a + c - 1) (u + v) := by
  unfold sourcePoissonVertical
  push_cast
  ring

/-- The exact triangular change of real heights in the product of the
three inverse Mellin integrals. -/
theorem sourcePoissonHeight_integral_shear (f g h : ℝ → ℂ) :
    (∫ p : SourcePoissonHeights, f p.1.1 * g p.1.2 * h (p.2 + p.1.2)
      ∂sourcePoissonHeightMeasure) =
    (∫ u : ℝ, f u) * (∫ u : ℝ, g u) * (∫ u : ℝ, h u) := by
  let e : SourcePoissonHeights ≃ᵐ SourcePoissonHeights :=
    { toEquiv :=
        { toFun := fun p => (p.1, p.2 + p.1.2)
          invFun := fun p => (p.1, p.2 - p.1.2)
          left_inv := fun p => by simp
          right_inv := fun p => by simp }
      measurable_toFun := measurable_fst.prodMk
        (measurable_snd.add (measurable_snd.comp measurable_fst))
      measurable_invFun := measurable_fst.prodMk
        (measurable_snd.sub (measurable_snd.comp measurable_fst)) }
  have he : MeasurePreserving e sourcePoissonHeightMeasure sourcePoissonHeightMeasure :=
    sourceLogRadial_shear_measurePreserving ((volume : Measure ℝ).prod volume)
      Prod.snd measurable_snd
  rw [show (∫ p : SourcePoissonHeights, f p.1.1 * g p.1.2 * h (p.2 + p.1.2)
        ∂sourcePoissonHeightMeasure) =
      ∫ p : SourcePoissonHeights, f p.1.1 * g p.1.2 * h p.2 ∂sourcePoissonHeightMeasure
      from he.integral_comp' (fun p => f p.1.1 * g p.1.2 * h p.2)]
  rw [sourcePoissonHeightMeasure,
    integral_prod_mul (fun p : ℝ × ℝ => f p.1 * g p.2) h, integral_prod_mul f g]

end
end ArtinMatthews.SourcePhysical
