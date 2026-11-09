module

public import ArtinMatthews.SourceFiniteSupportedFiber
public import ArtinMatthews.SourceFiniteWindowEuler


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory StandardAdelic
open scoped NumberField AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance actualEulerFiniteMeasurable : MeasurableSpace 𝔸ᶠ[K] := borel _
local instance actualEulerFiniteBorel : BorelSpace 𝔸ᶠ[K] := ⟨rfl⟩
local instance actualEulerCompletionMeasurable (P : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (P.adicCompletion K) := borel _
local instance actualEulerCompletionBorel (P : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (P.adicCompletion K) := ⟨rfl⟩

theorem sourceKPInitialHalfplane_exterior {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) :
    1 / 6 < s.re := by
  have hn : (0 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
  push_cast at hs
  linarith

theorem sourceKPFiniteCoordinateIntertwiner_eq_euler
    (g : SourceKPFiniteAdeleProjective K hζ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      S₀ ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      ∀ (s : ℂ), ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1 →
        ∀ t : sourceKPAdelicCoveringTorus K hζ,
          sourceKPFiniteCoordinateIntertwiner K hζ s g t.val.2 =
            sourceKPExteriorScattering S s *
              sourceKPFiniteWindowIntegral K
                (sourceKPFiniteCoordinateIntertwiningKernel K hζ s g t.val.2) S := by
  obtain ⟨a, S, ha, hS, hbad, hcompact⟩ :=
    sourceKPFiniteProjective_support_compact K hζ g (S₀ ∪ sourceHilbertSet K ∅)
  refine ⟨S, Finset.subset_union_left.trans hS, Finset.subset_union_right.trans hS,
    hbad, ?_⟩
  intro s hs t
  have hex := sourceKPInitialHalfplane_exterior K hs
  have hpos : 0 < s.re := lt_trans (by norm_num) hex
  have hf := sourceKPFiniteCoordinateIntertwiningKernel_integrable K hζ hs (1, g) t
  apply sourceKPFiniteWindowIntegral_eq_product_limit K S _ hf
    (fun P => sourceKPUnramifiedScatteringFactor P s) _
    (sourceKPUnramifiedScatteringFactor_hasProd_all K S hex)
  intro T P hPT hPS
  apply sourceKPFiniteWindow_integral_step K T P hPT _ hf
  intro r _
  have hHilbert : P ∉ sourceHilbertSet K ∅ := fun h =>
    hPS (hS (Finset.mem_union_right _ h))
  let P' : SourceExteriorPrime K ∅ := ⟨P, hHilbert⟩
  obtain ⟨h6, k, hk⟩ := hcompact P hPS
  have hpbad : P ∉ traceBadPlaces K := fun h => hPS (hbad h)
  have hlocal := sourceKPFiniteCoordinateFiber_of_integral_representative K hζ
    P' h6 a k hk s t r.val r.property hpbad hpos
  simpa only [ha] using hlocal

end
end ArtinMatthews
