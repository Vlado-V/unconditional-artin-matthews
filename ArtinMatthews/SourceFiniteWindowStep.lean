module

public import ArtinMatthews.SourceFiniteWindowFibers
public import ArtinMatthews.SourceFiniteIntertwinerFubini


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]

local instance windowStepFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance windowStepFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance windowStepCompletionMeasurable (P : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (P.adicCompletion K) := borel _
local instance windowStepCompletionBorel (P : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (P.adicCompletion K) := ⟨rfl⟩

def sourceKPFiniteWindowRemainderSet (P : HeightOneSpectrum (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (sourceKPFinitePlaceRemainder K P) :=
  {r | r.val ∈ sourceKPFiniteWindow K S}

theorem sourceKPFiniteWindowRemainderSet_measurable (P : HeightOneSpectrum (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MeasurableSet (sourceKPFiniteWindowRemainderSet K P S) :=
  ((sourceKPFiniteWindow_isClosed K S).preimage continuous_subtype_val).measurableSet

theorem sourceKPFiniteWindow_full_inner (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∈ S) (f : 𝔸ᶠ[K] → ℂ)
    (r : sourceKPFinitePlaceRemainder K P) :
    (∫ x : P.adicCompletion K, (sourceKPFiniteWindow K S).indicator f
      (sourceKPFiniteAdditiveSingle K P x + r.val) ∂sourceJacquetHaar K P) =
    (sourceKPFiniteWindowRemainderSet K P S).indicator
      (fun r => ∫ x : P.adicCompletion K,
        f (sourceKPFiniteAdditiveSingle K P x + r.val) ∂sourceJacquetHaar K P) r := by
  by_cases hr : r.val ∈ sourceKPFiniteWindow K S
  · rw [Set.indicator_of_mem (show r ∈ sourceKPFiniteWindowRemainderSet K P S from hr)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => Set.indicator_of_mem
      ((sourceKPFiniteWindow_single_add_of_mem K S P hP x r).mpr hr) f)
  · rw [Set.indicator_of_notMem (show r ∉ sourceKPFiniteWindowRemainderSet K P S from hr)]
    have he : (fun x : P.adicCompletion K => (sourceKPFiniteWindow K S).indicator f
        (sourceKPFiniteAdditiveSingle K P x + r.val)) = fun _ => 0 := by
      funext x
      exact Set.indicator_of_notMem
        (fun h => hr ((sourceKPFiniteWindow_single_add_of_mem K S P hP x r).mp h)) f
    rw [he, integral_zero]

theorem sourceKPFiniteWindow_unit_inner (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (f : 𝔸ᶠ[K] → ℂ)
    (r : sourceKPFinitePlaceRemainder K P) :
    (∫ x : P.adicCompletion K, (sourceKPFiniteWindow K (S.erase P)).indicator f
      (sourceKPFiniteAdditiveSingle K P x + r.val) ∂sourceJacquetHaar K P) =
    (sourceKPFiniteWindowRemainderSet K P S).indicator
      (fun r => ∫ x : P.adicCompletion K in (P.adicCompletionIntegers K : Set _),
        f (sourceKPFiniteAdditiveSingle K P x + r.val) ∂sourceJacquetHaar K P) r := by
  have hO : MeasurableSet (P.adicCompletionIntegers K : Set (P.adicCompletion K)) :=
    (Valued.isClosed_valuationSubring (P.adicCompletion K)).measurableSet
  by_cases hr : r.val ∈ sourceKPFiniteWindow K S
  · rw [Set.indicator_of_mem (show r ∈ sourceKPFiniteWindowRemainderSet K P S from hr),
      ← integral_indicator hO]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ P.adicCompletionIntegers K
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem
        ((sourceKPFiniteWindow_single_add_erase K S P x r).mpr ⟨hx, hr⟩)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem
        (fun h => hx ((sourceKPFiniteWindow_single_add_erase K S P x r).mp h).1)]
  · rw [Set.indicator_of_notMem (show r ∉ sourceKPFiniteWindowRemainderSet K P S from hr)]
    have he : (fun x : P.adicCompletion K => (sourceKPFiniteWindow K (S.erase P)).indicator f
        (sourceKPFiniteAdditiveSingle K P x + r.val)) = fun _ => 0 := by
      funext x
      exact Set.indicator_of_notMem
        (fun h => hr ((sourceKPFiniteWindow_single_add_erase K S P x r).mp h).2) f
    rw [he, integral_zero]

theorem sourceKPFiniteWindow_integral_full (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∈ S) (f : 𝔸ᶠ[K] → ℂ)
    (hf : Integrable f (sourceKPFiniteStandardHaar K)) :
    (∫ y in sourceKPFiniteWindow K S, f y ∂sourceKPFiniteStandardHaar K) =
      ∫ r in sourceKPFiniteWindowRemainderSet K P S,
        (∫ x : P.adicCompletion K, f (sourceKPFiniteAdditiveSingle K P x + r.val)
          ∂sourceJacquetHaar K P) ∂sourceKPFinitePlaceRemainderStandardHaar K P := by
  have h := sourceKPFiniteStandardHaar_integral_place K P ((sourceKPFiniteWindow K S).indicator f)
    (hf.indicator (sourceKPFiniteWindow_isClosed K S).measurableSet)
  rw [integral_indicator (sourceKPFiniteWindow_isClosed K S).measurableSet] at h
  simp_rw [sourceKPFiniteWindow_full_inner K S P hP f] at h
  rw [integral_indicator (sourceKPFiniteWindowRemainderSet_measurable K P S)] at h
  exact h

theorem sourceKPFiniteWindow_integral_unit (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (f : 𝔸ᶠ[K] → ℂ)
    (hf : Integrable f (sourceKPFiniteStandardHaar K)) :
    (∫ y in sourceKPFiniteWindow K (S.erase P), f y ∂sourceKPFiniteStandardHaar K) =
      ∫ r in sourceKPFiniteWindowRemainderSet K P S,
        (∫ x : P.adicCompletion K in (P.adicCompletionIntegers K : Set _),
          f (sourceKPFiniteAdditiveSingle K P x + r.val)
          ∂sourceJacquetHaar K P) ∂sourceKPFinitePlaceRemainderStandardHaar K P := by
  have h := sourceKPFiniteStandardHaar_integral_place K P ((sourceKPFiniteWindow K (S.erase P)).indicator f)
    (hf.indicator (sourceKPFiniteWindow_isClosed K (S.erase P)).measurableSet)
  rw [integral_indicator (sourceKPFiniteWindow_isClosed K (S.erase P)).measurableSet] at h
  simp_rw [sourceKPFiniteWindow_unit_inner K S P f] at h
  rw [integral_indicator (sourceKPFiniteWindowRemainderSet_measurable K P S)] at h
  exact h

theorem sourceKPFiniteWindow_integral_step (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∈ S) (f : 𝔸ᶠ[K] → ℂ)
    (hf : Integrable f (sourceKPFiniteStandardHaar K)) (c : ℂ)
    (hlocal : ∀ r : sourceKPFinitePlaceRemainder K P, r.val ∈ sourceKPFiniteWindow K S →
      (∫ x : P.adicCompletion K, f (sourceKPFiniteAdditiveSingle K P x + r.val)
        ∂sourceJacquetHaar K P) =
      c * ∫ x : P.adicCompletion K in (P.adicCompletionIntegers K : Set _),
        f (sourceKPFiniteAdditiveSingle K P x + r.val) ∂sourceJacquetHaar K P) :
    (∫ y in sourceKPFiniteWindow K S, f y ∂sourceKPFiniteStandardHaar K) =
      c * ∫ y in sourceKPFiniteWindow K (S.erase P), f y ∂sourceKPFiniteStandardHaar K := by
  rw [sourceKPFiniteWindow_integral_full K S P hP f hf,
    sourceKPFiniteWindow_integral_unit K S P f hf, ← integral_const_mul]
  apply setIntegral_congr_fun (sourceKPFiniteWindowRemainderSet_measurable K P S)
  intro r hr
  exact hlocal r hr

end
end ArtinMatthews
