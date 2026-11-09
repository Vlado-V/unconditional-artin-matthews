module

public import ArtinMatthews.SourceFiniteIntertwinerFubini


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance coordinateFiberCompletionMeasurable (P : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (P.adicCompletion K) := borel _
local instance coordinateFiberCompletionBorel (P : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (P.adicCompletion K) := ⟨rfl⟩

def sourceKPFiniteCoordinateScale (s : ℂ) (t : sourceKPAdelicCoveringTorus K hζ) : ℂ :=
  (sourceKPAdelicBorelModularHalf K hζ (sourceKPAdelicBorelTorusInclusion K hζ t))⁻¹ *
    sourceArchSphericalProduct K hζ s t.val.1 * sourceKPArchIntertwiningKernel K hζ s 1 0

theorem sourceKPFiniteCoordinateScale_ne_zero (s : ℂ) (t : sourceKPAdelicCoveringTorus K hζ) :
    sourceKPFiniteCoordinateScale K hζ s t ≠ 0 := by
  have hd : sourceKPAdelicBorelModularHalf K hζ
      (sourceKPAdelicBorelTorusInclusion K hζ t) ≠ 0 := by
    change (sourceKPIdeleComplexNorm K (1 / 2 : ℂ)
      (sourceKPAdelicTorusIdele K hζ
        (sourceKPAdelicBorelTorusProjection K hζ
          (sourceKPAdelicBorelTorusInclusion K hζ t))) : ℂ) ≠ 0
    exact Units.ne_zero _
  have ha : sourceArchSphericalProduct K hζ s t.val.1 ≠ 0 := by
    unfold sourceArchSphericalProduct
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => sourceKPArchSphericalSection_ne_zero s _)
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero hd) ha)
    (sourceKPArchIntertwiningKernel_ne_zero K hζ s 1 0)

theorem sourceKPAdelicCoordinateKernel_finite (s : ℂ)
    (g : SourceKPFiniteAdeleProjective K hζ) (t : sourceKPAdelicCoveringTorus K hζ)
    (x : 𝔸ᶠ[K]) :
    sourceKPAdelicCoordinateKernel K hζ s (1, g) t (0, x) =
      sourceKPFiniteCoordinateScale K hζ s t *
        sourceKPFiniteCoordinateIntertwiningKernel K hζ s g t.val.2 x := by
  exact sourceKPAdelicCoordinateKernel_arch_finite K hζ s (1, g) t (0, x)

theorem sourceKPAdelicCoordinateFiber_integral (P : HeightOneSpectrum (𝓞 K))
    (s : ℂ) (g : SourceKPFiniteAdeleProjective K hζ)
    (t : sourceKPAdelicCoveringTorus K hζ) (r : 𝔸ᶠ[K]) :
    (∫ x : P.adicCompletion K, sourceKPAdelicCoordinateKernel K hζ s (1, g) t
      (0, sourceKPFiniteAdditiveSingle K P x + r) ∂sourceJacquetHaar K P) =
    sourceKPFiniteCoordinateScale K hζ s t *
      ∫ x : P.adicCompletion K, sourceKPFiniteCoordinateIntertwiningKernel K hζ s g t.val.2
        (sourceKPFiniteAdditiveSingle K P x + r) ∂sourceJacquetHaar K P := by
  simp_rw [sourceKPAdelicCoordinateKernel_finite]
  exact integral_const_mul _ _

theorem sourceKPAdelicCoordinateFiber_unit_integral (P : HeightOneSpectrum (𝓞 K))
    (s : ℂ) (g : SourceKPFiniteAdeleProjective K hζ)
    (t : sourceKPAdelicCoveringTorus K hζ) (r : 𝔸ᶠ[K]) :
    (∫ x : P.adicCompletion K in (P.adicCompletionIntegers K : Set _),
      sourceKPAdelicCoordinateKernel K hζ s (1, g) t
        (0, sourceKPFiniteAdditiveSingle K P x + r) ∂sourceJacquetHaar K P) =
    sourceKPFiniteCoordinateScale K hζ s t *
      ∫ x : P.adicCompletion K in (P.adicCompletionIntegers K : Set _),
        sourceKPFiniteCoordinateIntertwiningKernel K hζ s g t.val.2
          (sourceKPFiniteAdditiveSingle K P x + r) ∂sourceJacquetHaar K P := by
  simp_rw [sourceKPAdelicCoordinateKernel_finite]
  exact integral_const_mul _ _

theorem sourceKPFiniteCoordinateFiber_relation_of_global (P : HeightOneSpectrum (𝓞 K))
    (s : ℂ) (g : SourceKPFiniteAdeleProjective K hζ)
    (t : sourceKPAdelicCoveringTorus K hζ) (r : 𝔸ᶠ[K]) (c : ℂ)
    (hglobal :
      (∫ x : P.adicCompletion K, sourceKPAdelicCoordinateKernel K hζ s (1, g) t
        (0, sourceKPFiniteAdditiveSingle K P x + r) ∂sourceJacquetHaar K P) =
      c * ∫ x : P.adicCompletion K in (P.adicCompletionIntegers K : Set _),
        sourceKPAdelicCoordinateKernel K hζ s (1, g) t
          (0, sourceKPFiniteAdditiveSingle K P x + r) ∂sourceJacquetHaar K P) :
    (∫ x : P.adicCompletion K, sourceKPFiniteCoordinateIntertwiningKernel K hζ s g t.val.2
      (sourceKPFiniteAdditiveSingle K P x + r) ∂sourceJacquetHaar K P) =
      c * ∫ x : P.adicCompletion K in (P.adicCompletionIntegers K : Set _),
        sourceKPFiniteCoordinateIntertwiningKernel K hζ s g t.val.2
          (sourceKPFiniteAdditiveSingle K P x + r) ∂sourceJacquetHaar K P := by
  rw [sourceKPAdelicCoordinateFiber_integral, sourceKPAdelicCoordinateFiber_unit_integral] at hglobal
  apply mul_left_cancel₀ (sourceKPFiniteCoordinateScale_ne_zero K hζ s t)
  calc
    _ = c * (sourceKPFiniteCoordinateScale K hζ s t * _) := hglobal
    _ = _ := by ring

end
end ArtinMatthews
