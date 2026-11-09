module

public import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpLocalization
public import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! Apply a bounded coefficient on a dominated compact localization,
then extend by zero as the literal measurable indicator. -/

namespace ArtinMatthews

open MeasureTheory Set Filter
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison
open scoped ENNReal

noncomputable section

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {μ ν : Measure X} {S : Set X}

def sourceLpRestrictZeroExtension (hS : MeasurableSet S) :
    Lp F 2 (μ.restrict S) →L[ℂ] Lp F 2 μ :=
  (LpLocalization.CM.Construction.lpSubtypeZeroExtension μ hS).toContinuousLinearMap.comp
    (Lp.compMeasurePreservingₗᵢ ℂ (Subtype.val : S → X)
      ⟨measurable_subtype_coe,map_comap_subtype_coe hS μ⟩).toContinuousLinearMap

theorem sourceLpRestrictZeroExtension_coe (hS : MeasurableSet S) (f : Lp F 2 (μ.restrict S)) :
    sourceLpRestrictZeroExtension hS f =ᵐ[μ] S.indicator f := by
  let hcoe : MeasurePreserving (Subtype.val : S → X) (μ.comap Subtype.val) (μ.restrict S) :=
    ⟨measurable_subtype_coe,map_comap_subtype_coe hS μ⟩
  let r := Lp.compMeasurePreserving (Subtype.val : S → X) hcoe f
  have hr := Lp.coeFn_compMeasurePreserving f hcoe
  change LpLocalization.CM.Construction.lpSubtypeZeroExtension μ hS r =ᵐ[μ] S.indicator f
  refine (LpLocalization.CM.Construction.lpSubtypeZeroExtension_coeFn μ hS r).trans ?_
  refine (LpLocalization.CM.Construction.subtypeZeroExtension_ae_eq μ hS hr).trans ?_
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ S
  · simp only [LpLocalization.CM.Construction.subtypeZeroExtension_apply_mem _ hx,indicator_of_mem hx,Function.comp_apply]
  · rw [LpLocalization.CM.Construction.subtypeZeroExtension_apply_notMem _ hx,indicator_of_notMem hx]

def sourceLpLocalizedField (hS : MeasurableSet S) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hdom : μ.restrict S ≤ c • ν) (A : X → F →L[ℝ] F)
    (hA : AEStronglyMeasurable A (μ.restrict S))
    {C : ℝ} (hC : ∀ᵐ x ∂(μ.restrict S), ‖A x‖ ≤ C) :
    Lp F 2 ν →L[ℝ] Lp F 2 μ :=
  ((sourceLpRestrictZeroExtension hS).restrictScalars ℝ).comp
    ((LpCoefficients.CM.Construction.boundedFieldLp A hA hC).comp (Lp.LpToLpOfMeasureLeSMul hc hdom))

theorem sourceLpLocalizedField_coe (hS : MeasurableSet S) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hdom : μ.restrict S ≤ c • ν) (A : X → F →L[ℝ] F)
    (hA : AEStronglyMeasurable A (μ.restrict S))
    {C : ℝ} (hC : ∀ᵐ x ∂(μ.restrict S), ‖A x‖ ≤ C) (f : Lp F 2 ν) :
    sourceLpLocalizedField hS hc hdom A hA hC f =ᵐ[μ] S.indicator (fun x => A x (f x)) := by
  let v : Lp F 2 (μ.restrict S) := Lp.LpToLpOfMeasureLeSMul hc hdom f
  let w := LpCoefficients.CM.Construction.boundedFieldLp A hA hC v
  have hw : w =ᵐ[μ.restrict S] fun x => A x (f x) := by
    filter_upwards [LpCoefficients.CM.Construction.boundedFieldLp_coe A hA hC v,
      Lp.coeFn_LpToLpOfMeasureLeSMul hc hdom f] with x hwx hvx
    exact hwx.trans (congrArg (A x) hvx)
  change sourceLpRestrictZeroExtension hS w =ᵐ[μ] _
  refine (sourceLpRestrictZeroExtension_coe hS w).trans ?_
  filter_upwards [(ae_restrict_iff' hS).mp hw] with x hx
  by_cases hxS : x ∈ S
  · rw [indicator_of_mem hxS,indicator_of_mem hxS,hx hxS]
  · rw [indicator_of_notMem hxS,indicator_of_notMem hxS]

end
end ArtinMatthews
