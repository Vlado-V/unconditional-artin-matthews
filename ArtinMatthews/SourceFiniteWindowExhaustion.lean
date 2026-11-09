module

public import ArtinMatthews.SourceFiniteIntertwinerIntegrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory Filter
open scoped NumberField AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K]

local instance finiteWindowFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel 𝔸ᶠ[K]
local instance finiteWindowFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩

def sourceKPFiniteWindow (S : Finset (HeightOneSpectrum (𝓞 K))) : Set 𝔸ᶠ[K] :=
  {x | ∀ P, P ∉ S → x P ∈ P.adicCompletionIntegers K}

theorem sourceKPFiniteWindow_isClosed (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsClosed (sourceKPFiniteWindow K S) := by
  have he : sourceKPFiniteWindow K S =
      ⋂ P : HeightOneSpectrum (𝓞 K), ⋂ (_ : P ∉ S),
        {x : 𝔸ᶠ[K] | x P ∈ P.adicCompletionIntegers K} := by
    ext x
    simp only [sourceKPFiniteWindow, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [he]
  exact isClosed_iInter (fun P => isClosed_iInter (fun _ =>
    (Valued.isClosed_valuationSubring (P.adicCompletion K)).preimage
      (RestrictedProduct.continuous_eval P)))

theorem sourceKPFiniteWindow_mono : Monotone (sourceKPFiniteWindow K) := by
  intro S T hST x hx P hP
  exact hx P (fun h => hP (hST h))

theorem sourceKPFiniteWindow_eventually_mem (x : 𝔸ᶠ[K]) :
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 K)) in atTop, x ∈ sourceKPFiniteWindow K S := by
  classical
  have hbad : {P : HeightOneSpectrum (𝓞 K) | x P ∉ P.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp x.property
  apply Filter.eventually_atTop.2
  refine ⟨hbad.toFinset, ?_⟩
  intro S hS P hP
  by_contra h
  apply hP
  exact hS (by simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using h)

theorem sourceKPFiniteWindow_union :
    (⋃ S : Finset (HeightOneSpectrum (𝓞 K)), sourceKPFiniteWindow K S) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  obtain ⟨S, hS⟩ := (sourceKPFiniteWindow_eventually_mem K x).exists
  exact ⟨S, hS⟩

theorem sourceKPFiniteWindow_integral_tendsto (μ : Measure 𝔸ᶠ[K]) (f : 𝔸ᶠ[K] → ℂ)
    (hf : Integrable f μ) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      ∫ x in sourceKPFiniteWindow K S, f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hlim : ∀ᵐ x ∂μ, Tendsto
      (fun S : Finset (HeightOneSpectrum (𝓞 K)) => (sourceKPFiniteWindow K S).indicator f x)
      atTop (𝓝 (f x)) := by
    apply Filter.Eventually.of_forall
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [sourceKPFiniteWindow_eventually_mem K x] with S hS
    simp only [Set.indicator_of_mem hS]
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := (atTop : Filter (Finset (HeightOneSpectrum (𝓞 K)))))
    (F := fun S => (sourceKPFiniteWindow K S).indicator f) (f := f) (fun x => ‖f x‖)
    (Filter.Eventually.of_forall (fun S =>
      hf.aestronglyMeasurable.indicator (sourceKPFiniteWindow_isClosed K S).measurableSet))
    (Filter.Eventually.of_forall (fun S => Filter.Eventually.of_forall (fun x =>
      norm_indicator_le_norm_self _ _))) hf.norm hlim
  have he (S : Finset (HeightOneSpectrum (𝓞 K))) :
      (∫ x, (sourceKPFiniteWindow K S).indicator f x ∂μ) =
        ∫ x in sourceKPFiniteWindow K S, f x ∂μ :=
    integral_indicator (sourceKPFiniteWindow_isClosed K S).measurableSet
  simp_rw [he] at h
  exact h

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFiniteIntertwiner_window_tendsto
    {s : ℂ} (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1)
    (g : SourceKPFiniteAdeleProjective K hζ) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      ∫ x in sourceKPFiniteWindow K S, sourceKPFiniteIntertwiningKernel K hζ s g x
        ∂sourceKPFiniteStandardHaar K) atTop (𝓝 (sourceKPFiniteIntertwiner K hζ s g)) :=
  sourceKPFiniteWindow_integral_tendsto K _ _
    (sourceKPFiniteIntertwiningKernel_integrable K hζ hs g)

end
end ArtinMatthews
