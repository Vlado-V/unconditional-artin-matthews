module

public import ArtinMatthews.SourceFiniteWindowHolomorphic
public import ArtinMatthews.SourceFiniteSupportedFiber


set_option backward.privateInPublic true
@[expose] public section

/-! The actual tame place step on windows throughout the positive half-plane. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical
open scoped NumberField AdeleRing Classical

noncomputable section

variable (K : Type) [Field K] [NumberField K]

local instance windowTameFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance windowTameFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance windowTameCompletionMeasurable (P : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (P.adicCompletion K) := borel _
local instance windowTameCompletionBorel (P : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (P.adicCompletion K) := ⟨rfl⟩

theorem sourceKPFiniteWindow_integral_step_of_integrableOn
    (S : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∈ S) (f : 𝔸ᶠ[K] → ℂ)
    (hf : IntegrableOn f (sourceKPFiniteWindow K S) (sourceKPFiniteStandardHaar K)) (c : ℂ)
    (hlocal : ∀ r : sourceKPFinitePlaceRemainder K P, r.val ∈ sourceKPFiniteWindow K S →
      (∫ x : P.adicCompletion K, f (sourceKPFiniteAdditiveSingle K P x + r.val)
        ∂sourceJacquetHaar K P) =
      c * ∫ x : P.adicCompletion K in (P.adicCompletionIntegers K : Set _),
        f (sourceKPFiniteAdditiveSingle K P x + r.val) ∂sourceJacquetHaar K P) :
    (∫ y in sourceKPFiniteWindow K S, f y ∂sourceKPFiniteStandardHaar K) =
      c * ∫ y in sourceKPFiniteWindow K (S.erase P), f y ∂sourceKPFiniteStandardHaar K := by
  let f₀ := (sourceKPFiniteWindow K S).indicator f
  have hS := (sourceKPFiniteWindow_isClosed K S).measurableSet
  have hf₀ : Integrable f₀ (sourceKPFiniteStandardHaar K) := (integrable_indicator_iff hS).mpr hf
  have h := sourceKPFiniteWindow_integral_step K S P hP f₀ hf₀ c (by
    intro r hr
    have he : (fun x : P.adicCompletion K => f₀ (sourceKPFiniteAdditiveSingle K P x + r.val)) =
        fun x => f (sourceKPFiniteAdditiveSingle K P x + r.val) := by
      funext x
      exact Set.indicator_of_mem ((sourceKPFiniteWindow_single_add_of_mem K S P hP x r).mpr hr) f
    simpa only [he] using hlocal r hr)
  calc
    _ = ∫ y in sourceKPFiniteWindow K S, f₀ y ∂sourceKPFiniteStandardHaar K :=
      setIntegral_congr_fun hS (fun _ hy => (Set.indicator_of_mem hy f).symm)
    _ = c * ∫ y in sourceKPFiniteWindow K (S.erase P), f₀ y ∂sourceKPFiniteStandardHaar K := h
    _ = _ := by
      apply congrArg (fun z : ℂ => c * z)
      apply setIntegral_congr_fun (sourceKPFiniteWindow_isClosed K (S.erase P)).measurableSet
      intro y hy
      exact Set.indicator_of_mem
        (sourceKPFiniteWindow_mono K (Finset.erase_subset P S) hy) f

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFiniteWindowIntertwiner_tame_step {s : ℂ} (hs : 0 < s.re)
    (g : SourceKPFiniteAdeleProjective K hζ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : SourceExteriorPrime K ∅) (hP : P.val ∈ S) (hbad : P.val ∉ traceBadPlaces K)
    (hbase : sourceKPAdelicLocalBase K hζ P.val (1, g) = 1) :
    sourceKPFiniteWindowIntegral K (sourceKPFiniteIntertwiningKernel K hζ s g) S =
      sourceKPUnramifiedScatteringFactor P.val s *
        sourceKPFiniteWindowIntegral K (sourceKPFiniteIntertwiningKernel K hζ s g) (S.erase P.val) := by
  unfold sourceKPFiniteWindowIntegral
  apply sourceKPFiniteWindow_integral_step_of_integrableOn K S P.val hP _
    (sourceKPFiniteIntertwiningKernel_window_integrable K hζ hs g S)
  intro r _
  simpa only [sourceLocalBall_zero] using
    sourceKPLocalFiniteKernel_integral_eq_factor_unit_ball K hζ ∅ P s g hbase
      r.val r.property hbad hs

theorem sourceKPFiniteWindowIntertwiner_tame_step_integralRepresentative {s : ℂ} (hs : 0 < s.re)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (P : SourceExteriorPrime K ∅) (hP : P.val ∈ S) (hbad : P.val ∉ traceBadPlaces K)
    (h6 : (6 : 𝓞 K) ∉ P.val.asIdeal)
    (a : SourceKPFiniteAdeleCover K hζ) (k : SourceFiniteKP2Integral K P.val)
    (hk : k.val = sourceKPAdeleMatrixAt K P.val a.base) :
    sourceKPFiniteWindowIntegral K
        (sourceKPFiniteIntertwiningKernel K hζ s (sourceKPFiniteAdeleProjectiveMk K hζ a)) S =
      sourceKPUnramifiedScatteringFactor P.val s * sourceKPFiniteWindowIntegral K
        (sourceKPFiniteIntertwiningKernel K hζ s (sourceKPFiniteAdeleProjectiveMk K hζ a)) (S.erase P.val) := by
  let g := sourceKPFiniteAdeleProjectiveMk K hζ a
  let g' := (sourceKPFiniteCompactRemove K hζ P.val h6 g k).2
  have hb : sourceKPAdelicLocalBase K hζ P.val (1, g') = 1 := by
    change sourceKPAdelicLocalBase K hζ P.val
      (1, (sourceKPFiniteCompactRemove K hζ P.val h6 g k).2) = 1
    rw [← sourceKPFiniteCompactRemove_eq_pair]
    exact sourceKPFiniteCompactRemove_base K hζ P.val h6 a k hk
  have he : sourceKPFiniteIntertwiningKernel K hζ s g = sourceKPFiniteIntertwiningKernel K hζ s g' :=
    funext (sourceKPFiniteCompactRemove_kernel K hζ P.val h6 s g k)
  change sourceKPFiniteWindowIntegral K (sourceKPFiniteIntertwiningKernel K hζ s g) S =
    sourceKPUnramifiedScatteringFactor P.val s * sourceKPFiniteWindowIntegral K
      (sourceKPFiniteIntertwiningKernel K hζ s g) (S.erase P.val)
  rw [he]
  exact sourceKPFiniteWindowIntertwiner_tame_step K hζ hs g' S P hP hbad hb

end
end ArtinMatthews
