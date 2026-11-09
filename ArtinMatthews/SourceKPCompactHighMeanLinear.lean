module

public import ArtinMatthews.SourceKPCompactHighOrbitL2
public import Mathlib.Order.Filter.Finite


set_option backward.privateInPublic true
@[expose] public section

/-! The literal normalized unipotent mean respects native representatives
and finite complex-linear combinations on the full high section. -/

namespace ArtinMatthews
open NumberField MeasureTheory Set Filter
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (A : ℝ)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μS" => Measure.restrict (sourceKPHighRepresentativeHaar K hζ A) (sourceKPCuspBandHighSection K hζ A)
local notation "μD" => Measure.restrict (sourceKPAdelicTraceProduct K) (sourceKPAdelicFundamentalDomain K)
local notation "orb" => sourceKPCompactHighOrbit K hζ A
local notation "mean" => sourceKPCompactHighUnipotentMean K hζ A
local instance sourceKPCompactHighMeanLinearAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _

theorem sourceKPCompactHighUnipotentMean_congr_ae (hA : 1 < A) {F G : Y → ℂ}
    (hFG : F =ᵐ[μY] G) : mean F =ᵐ[μS] mean G := by
  filter_upwards [sourceKPCompactHighOrbit_congr_ae K hζ A hA hFG] with x hx
  exact integral_congr_ae hx

theorem sourceKPCompactHighUnipotentMean_add_ae (hA : 1 < A) (F G : Y → ℂ)
    (hF : MemLp F 2 μY) (hG : MemLp G 2 μY) :
    mean (fun y => F y + G y) =ᵐ[μS] fun x => mean F x + mean G x := by
  filter_upwards [sourceKPCompactHighOrbit_integrable_ae K hζ A hA F hF,
    sourceKPCompactHighOrbit_integrable_ae K hζ A hA G hG] with x hFx hGx
  exact integral_add hFx hGx

theorem sourceKPCompactHighUnipotentMean_smul_ae (c : ℂ) (F : Y → ℂ) :
    mean (fun y => c • F y) =ᵐ[μS] fun x => c • mean F x := by
  exact Eventually.of_forall fun x => integral_smul (μ := μD) c (fun a => F (orb x a))

theorem sourceKPCompactHighUnipotentMean_finsetSum_ae {ι : Type*} (hA : 1 < A)
    (S : Finset ι) (F : ι → Y → ℂ) (hF : ∀ i ∈ S, MemLp (F i) 2 μY) :
    mean (fun y => ∑ i ∈ S, F i y) =ᵐ[μS] fun x => ∑ i ∈ S, mean (F i) x := by
  have hfi : ∀ᵐ x ∂μS, ∀ i ∈ S, Integrable (fun a => F i (orb x a)) μD :=
    (Filter.eventually_all_finset S).2 fun i hi =>
      sourceKPCompactHighOrbit_integrable_ae K hζ A hA (F i) (hF i hi)
  filter_upwards [hfi] with x hx
  exact integral_finsetSum S hx

end
end ArtinMatthews
