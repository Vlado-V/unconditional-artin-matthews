module

public import ArtinMatthews.SourceKPCuspProductMeasure
public import ArtinMatthews.UnitTorusLocalRellich


set_option backward.privateInPublic true
@[expose] public section

/-! Fubini in the actual native principal cusp cell, with the same
positive Haar scalar as the geometric coordinate theorem. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory SourceHyperbolicGreen
open scoped NumberField AdeleRing ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)

local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd

def sourceKPCuspNativeBand (B : Set (V → ℝ)) : Set X :=
  (E).symm ⁻¹' ((Set.univ.pi fun _ : I => Set.Ioc (0:ℝ) 1) ×ˢ B)

theorem sourceKPCuspNativeBand_measurable (B : Set (V → ℝ)) (hB : MeasurableSet B) :
    MeasurableSet (sourceKPCuspNativeBand K hζ d hd B) :=
  ((MeasurableSet.univ_pi fun _ => measurableSet_Ioc).prod hB).preimage (E).symm.continuous.measurable

theorem sourceKPCuspNativeBand_integral
    (c : ℝ≥0) (hc : 0 < c)
    (hm : Measure.map (E).symm (productVolume V) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K))
    (B : Set (V → ℝ)) (hB : MeasurableSet B)
    (f : X → ℂ) (hf : IntegrableOn f (sourceKPCuspNativeBand K hζ d hd B) (productVolume V)) :
    (∫ p in sourceKPCuspNativeBand K hζ d hd B, f p ∂productVolume V) =
      (c:ℂ) * ∫ y in B, ∫ x : I → ℝ, f (E (x,y)) ∂unitTorusUnitCellMeasure I
        ∂sourceKPCuspProductHeightMeasure K := by
  let S := sourceKPCuspNativeBand K hζ d hd B
  let μ := (productVolume V).restrict S
  let e := (E).symm.toHomeomorph.toMeasurableEquiv
  let G : (I → ℝ) × (V → ℝ) → ℂ := fun p => f (E p)
  letI sourceNativeBaseCellFinite : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) 1)) :=
    ⟨by simp⟩
  letI sourceNativeCellFinite : IsFiniteMeasure (unitTorusUnitCellMeasure I) := by
    change IsFiniteMeasure (Measure.pi (fun _ : I => (volume : Measure ℝ).restrict (Set.Ioc (0:ℝ) 1)))
    infer_instance
  have hep (p : X) : E (e p) = p := (E).apply_symm_apply p
  have heq : (fun p : X => G (e p)) = f := by
    funext p
    exact congrArg f (hep p)
  have hmap : Measure.map e μ = (c:ℝ≥0∞) •
      (unitTorusUnitCellMeasure I).prod ((sourceKPCuspProductHeightMeasure K).restrict B) :=
    sourceKPCuspProductCoordinates_map_restrict_unitCell K hζ d hd c hm B hB
  have hi : Integrable G (Measure.map e μ) := by
    apply (integrable_map_equiv e G).mpr
    change Integrable (fun p : X => G (e p)) μ
    rw [heq]
    exact hf
  rw [hmap] at hi
  have hi' : Integrable G
      ((unitTorusUnitCellMeasure I).prod ((sourceKPCuspProductHeightMeasure K).restrict B)) :=
    (integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).mp hi
  calc
    _ = ∫ p, G p ∂Measure.map e μ := by
      rw [integral_map_equiv e G]
      rw [heq]
    _ = (c:ℂ) * ∫ p, G p
        ∂(unitTorusUnitCellMeasure I).prod ((sourceKPCuspProductHeightMeasure K).restrict B) := by
      rw [hmap,integral_smul_measure]
      simp only [ENNReal.coe_toReal,Complex.real_smul]
    _ = _ := congrArg (fun z : ℂ => (c:ℂ)*z) (integral_prod_symm G hi')

end
end ArtinMatthews
