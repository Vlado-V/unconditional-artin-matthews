module

public import ArtinMatthews.SourceKPCoupledCompactKernel
public import ArtinMatthews.SourceFiniteWindowEuler


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact-window integral equals the positive mass of
the simultaneous wild cylinder, in the global standard Haar measure. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance coupledBaseFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance coupledBaseFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩

local notation "Oᶠ" => IntegralAdeles.Construction.finiteIntegralRing K
local notation "C₀" => sourceKPCoupledDeepCylinder K (sixthWildPrimes K)
local notation "μ₀" => sourceKPFiniteStandardHaar K
local notation "g₀" => sourceKPCoupledWildWeyl K hζ

theorem sourceKPCoupledWindow_empty :
    sourceKPFiniteWindow K ∅ = (Oᶠ : Set 𝔸ᶠ[K]) := by
  ext x
  change (∀ P, P ∉ (∅ : Finset _) → x P ∈ P.adicCompletionIntegers K) ↔
    ∀ P, x P ∈ P.adicCompletionIntegers K
  simp

theorem sourceKPCoupledWindowIntegral_empty (s : ℂ) :
    sourceKPFiniteWindowIntegral K (sourceKPFiniteIntertwiningKernel K hζ s (g₀).2) ∅ =
      ((μ₀).real C₀ : ℂ) := by
  have hC := sourceKPCoupledDeepCylinder_measurable K (sixthWildPrimes K)
  have hO := (IntegralAdeles.Construction.isOpen_finiteIntegralRing K).measurableSet
  have hCO : C₀ ⊆ (Oᶠ : Set 𝔸ᶠ[K]) := fun _ hx => hx.1
  unfold sourceKPFiniteWindowIntegral
  rw [sourceKPCoupledWindow_empty K]
  calc
    _ = ∫ x in (Oᶠ : Set 𝔸ᶠ[K]), (C₀).indicator (fun _ => (1 : ℂ)) x ∂μ₀ :=
      setIntegral_congr_fun hO (sourceKPCoupledCompactKernel_indicator K hζ s)
    _ = _ := by
      rw [integral_indicator hC, integral_const, Measure.real, Measure.restrict_apply_univ,
        Measure.restrict_apply hC, Set.inter_eq_left.mpr hCO]
      simp [Complex.real_smul, Measure.real]

end
end ArtinMatthews
