module

public import ArtinMatthews.SourceKPCuspNativeIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Integrability transports through the actual principal-cell chart before
applying Fubini, with its fixed Haar normalization. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory SourceHyperbolicGreen
open scoped NumberField AdeleRing ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd

theorem sourceKPCuspNativeBand_integrable_product
    (c : ℝ≥0) (hc : 0 < c)
    (hm : Measure.map (E).symm (productVolume V) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K))
    (B : Set (InfinitePlace K → ℝ)) (hB : MeasurableSet B)
    (f : ProductSpace V → ℂ)
    (hf : IntegrableOn f (sourceKPCuspNativeBand K hζ d hd B) (productVolume V)) :
    Integrable (fun p : (I → ℝ) × (V → ℝ) => f (E p))
      ((unitTorusUnitCellMeasure I).prod ((sourceKPCuspProductHeightMeasure K).restrict B)) := by
  let μ := (productVolume V).restrict (sourceKPCuspNativeBand K hζ d hd B)
  let e := (E).symm.toHomeomorph.toMeasurableEquiv
  let F : (I → ℝ) × (V → ℝ) → ℂ := fun p => f (E p)
  have he (p : ProductSpace V) : F (e p) = f p := congrArg f ((E).apply_symm_apply p)
  have hi : Integrable F (Measure.map e μ) := by
    apply (integrable_map_equiv e F).mpr
    exact hf.congr (Filter.Eventually.of_forall fun p => (he p).symm)
  have hmap : Measure.map e μ = (c:ℝ≥0∞) •
      (unitTorusUnitCellMeasure I).prod ((sourceKPCuspProductHeightMeasure K).restrict B) :=
    sourceKPCuspProductCoordinates_map_restrict_unitCell K hζ d hd c hm B hB
  rw [hmap] at hi
  exact (integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).mp hi

end
end ArtinMatthews
