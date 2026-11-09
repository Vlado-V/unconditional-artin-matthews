module

public import ArtinMatthews.SourceArchIntertwinerProduct


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory SourceArchJacquet Matrix
open scoped NumberField AdeleRing MatrixGroups BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance finiteIntertwinerAdelicMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance finiteIntertwinerAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance finiteIntertwinerFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance finiteIntertwinerFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance finiteIntertwinerCompletionMeasurable (v : InfinitePlace K) : MeasurableSpace v.Completion := borel _
local instance finiteIntertwinerCompletionBorel (v : InfinitePlace K) : BorelSpace v.Completion := ⟨rfl⟩
local instance finiteIntertwinerCompletionSecondCountable (v : InfinitePlace K) : SecondCountableTopology v.Completion := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.secondCountableTopology
  · exact (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.secondCountableTopology
local instance finiteIntertwinerInfiniteMeasurable : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ v : InfinitePlace K, v.Completion))
local instance finiteIntertwinerInfiniteBorel : BorelSpace (InfiniteAdeleRing K) := by
  change BorelSpace (∀ v : InfinitePlace K, v.Completion)
  infer_instance

theorem sourceKPArchSphericalSection_ne_zero (s : ℂ) (g : PGL(2, ℂ)) :
    sourceArchSphericalSection s g ≠ 0 := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective g
  rw [sourceArchSphericalSection_mk, sourceArchSphericalGL]
  exact Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr (sourceArchHeight_pos g).ne'))

theorem sourceKPArchIntertwiningKernel_ne_zero (s : ℂ)
    (g : PGL(2, InfiniteAdeleRing K)) (x : InfiniteAdeleRing K) :
    sourceKPArchIntertwiningKernel K hζ s g x ≠ 0 := by
  rw [sourceKPArchIntertwiningKernel_product]
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => sourceKPArchSphericalSection_ne_zero s _)

include hζ in
theorem sourceKPTraceProduct_finite_integrable
    (f : InfiniteAdeleRing K → ℂ) (g : 𝔸ᶠ[K] → ℂ) (hf : ∀ x, f x ≠ 0)
    (hfg : Integrable (fun y : 𝔸[K] => f y.1 * g y.2) (sourceKPAdelicTraceProduct K)) :
    Integrable g (sourceKPFiniteStandardHaar K) := by
  let := source_isTotallyComplex K hζ
  have hc (v : InfinitePlace K) : InfinitePlace.IsComplex v := IsTotallyComplex.isComplex v
  let e := (OAI.RepresentationTheory.Weil.AdelicSplitting.CompactQuotient.Construction.adelicMixedHomeomorph K).toMeasurableEquiv
  let a := (OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph K).toMeasurableEquiv
  have ha : (a : InfiniteAdeleRing K → mixedEmbedding.mixedSpace K) =
      InfiniteAdeleRing.ringEquiv_mixedSpace K := by
    funext x
    rfl
  have hm : (sourceKPArchSelfDualProduct K).map a = sourceKPArchStandardHaar K := by
    rw [ha]
    exact sourceKPArchSelfDualProduct_mixedSpace K hc
  let : ((sourceKPArchSelfDualProduct K).map a).IsAddHaarMeasure := by
    rw [hm]
    infer_instance
  change Integrable (fun y : 𝔸[K] => f y.1 * g y.2)
    (Measure.map e.symm (((sourceKPArchSelfDualProduct K).map a).prod
      (sourceKPFiniteStandardHaar K))) at hfg
  have hp := (integrable_map_equiv e.symm (fun y : 𝔸[K] => f y.1 * g y.2)).mp hfg
  change Integrable (fun p : mixedEmbedding.mixedSpace K × 𝔸ᶠ[K] =>
    f (a.symm p.1) * g p.2) (((sourceKPArchSelfDualProduct K).map a).prod
      (sourceKPFiniteStandardHaar K)) at hp
  obtain ⟨x, hx⟩ := hp.prod_right_ae.exists
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (hf (a.symm x))) g).mp hx

theorem sourceKPFiniteIntertwiningKernel_integrable {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPFiniteAdeleProjective K hζ) :
    Integrable (sourceKPFiniteIntertwiningKernel K hζ s g) (sourceKPFiniteStandardHaar K) := by
  apply sourceKPTraceProduct_finite_integrable K hζ
    (sourceKPArchIntertwiningKernel K hζ s 1)
    (sourceKPFiniteIntertwiningKernel K hζ s g)
    (sourceKPArchIntertwiningKernel_ne_zero K hζ s 1)
  have h := sourceKPAdelicIntertwiningKernel_trace_integrable K hζ hs (1, g)
  exact h.congr (Filter.Eventually.of_forall (fun y =>
    sourceKPAdelicIntertwiningKernel_arch_finite K hζ s (1, g) y))

end
end ArtinMatthews
