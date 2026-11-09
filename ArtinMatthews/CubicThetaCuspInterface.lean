module

public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp


set_option backward.privateInPublic true
@[expose] public section

/-! Convert uniform normalized rational-cusp limits to Mathlib's cusp predicate.
This supplies no slash invariance and makes no modularity assertion. -/
noncomputable section
namespace ArtinMatthews

open scoped MatrixGroups Topology
open Complex UpperHalfPlane Filter ModularForm

/-- Weight-one normalized limits at integral cusp representatives give the
native vanishing predicate at every rational cusp. -/
theorem isZeroAt_of_weight_one_cusp_limits (f : ℍ → ℂ)
    (hf : ∀ γ : SL(2, ℤ),
      Tendsto (fun τ : ℍ => f (γ • τ) /
        ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ))) atImInfty (𝓝 0))
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : OnePoint.IsZeroAt c f 1 := by
  apply (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr
  intro γ _
  change Tendsto (f ∣[(1 : ℤ)] γ) atImInfty (𝓝 0)
  simpa only [ModularForm.SL_slash_def, ModularGroup.denom_apply,
    zpow_neg_one, div_eq_mul_inv] using hf γ

/-- Arithmetic subgroups have precisely the rational cusps, so the same proved
limits supply their native cusp-vanishing field. -/
theorem isZeroAt_arithmetic_of_weight_one_cusp_limits (f : ℍ → ℂ)
    (hf : ∀ γ : SL(2, ℤ),
      Tendsto (fun τ : ℍ => f (γ • τ) /
        ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ))) atImInfty (𝓝 0))
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    {c : OnePoint ℝ} (hc : IsCusp c Γ) : OnePoint.IsZeroAt c f 1 :=
  isZeroAt_of_weight_one_cusp_limits f hf
    ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ).mp hc)

end ArtinMatthews
