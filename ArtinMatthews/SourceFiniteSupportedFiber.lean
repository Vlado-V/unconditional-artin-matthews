module

public import ArtinMatthews.SourceFiniteCompactRemoval
public import ArtinMatthews.SourceFiniteCoordinateLocal


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory StandardAdelic
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance supportedFiberCompletionMeasurable (P : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (P.adicCompletion K) := borel _
local instance supportedFiberCompletionBorel (P : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (P.adicCompletion K) := ⟨rfl⟩

theorem sourceKPFiniteCoordinateFiber_of_integral_representative
    (P : SourceExteriorPrime K ∅) (h6 : (6 : 𝓞 K) ∉ P.val.asIdeal)
    (a : SourceKPFiniteAdeleCover K hζ) (k : SourceFiniteKP2Integral K P.val)
    (hk : k.val = sourceKPAdeleMatrixAt K P.val a.base)
    (s : ℂ) (t : sourceKPAdelicCoveringTorus K hζ)
    (r : 𝔸ᶠ[K]) (hr : r P.val = 0)
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) :
    (∫ x : P.val.adicCompletion K,
      sourceKPFiniteCoordinateIntertwiningKernel K hζ s
        (sourceKPFiniteAdeleProjectiveMk K hζ a) t.val.2
        (sourceKPFiniteAdditiveSingle K P.val x + r) ∂sourceJacquetHaar K P.val) =
      sourceKPUnramifiedScatteringFactor P.val s *
        ∫ x : P.val.adicCompletion K in (P.val.adicCompletionIntegers K : Set _),
          sourceKPFiniteCoordinateIntertwiningKernel K hζ s
            (sourceKPFiniteAdeleProjectiveMk K hζ a) t.val.2
            (sourceKPFiniteAdditiveSingle K P.val x + r) ∂sourceJacquetHaar K P.val := by
  let g := sourceKPFiniteAdeleProjectiveMk K hζ a
  let g' := (sourceKPFiniteCompactRemove K hζ P.val h6 g k).2
  have hg : sourceKPAdelicLocalBase K hζ P.val (1, g') = 1 := by
    change sourceKPAdelicLocalBase K hζ P.val
      (1, (sourceKPFiniteCompactRemove K hζ P.val h6 g k).2) = 1
    rw [← sourceKPFiniteCompactRemove_eq_pair]
    exact sourceKPFiniteCompactRemove_base K hζ P.val h6 a k hk
  have he (x : 𝔸ᶠ[K]) :
      sourceKPFiniteCoordinateIntertwiningKernel K hζ s g t.val.2 x =
        sourceKPFiniteCoordinateIntertwiningKernel K hζ s g' t.val.2 x :=
    sourceKPFiniteCompactRemove_coordinate_kernel K hζ P.val h6 s g t.val.2 k x
  have hl := sourceKPFiniteCoordinateFiber_relation K hζ ∅ P s g' hg t r hr hP hs
  calc
    _ = ∫ x : P.val.adicCompletion K,
        sourceKPFiniteCoordinateIntertwiningKernel K hζ s g' t.val.2
          (sourceKPFiniteAdditiveSingle K P.val x + r) ∂sourceJacquetHaar K P.val :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x =>
        he (sourceKPFiniteAdditiveSingle K P.val x + r)))
    _ = _ := hl
    _ = _ := congrArg (fun z : ℂ => sourceKPUnramifiedScatteringFactor P.val s * z)
      (integral_congr_ae (Filter.Eventually.of_forall (fun x =>
        (he (sourceKPFiniteAdditiveSingle K P.val x + r)).symm)))

end
end ArtinMatthews
