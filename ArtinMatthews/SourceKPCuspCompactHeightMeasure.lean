module

public import ArtinMatthews.SourceKPCuspNativeFrequency
public import ArtinMatthews.SourceKPCuspNativeIntegral
public import ArtinMatthews.SourceHyperbolicH1Measure


set_option backward.privateInPublic true
@[expose] public section

/-! The actual product height measure is finite on every compact positive
height set. The proof uses its already established native-coordinate measure. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory SourceHyperbolicGreen
open scoped NumberField AdeleRing ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)

local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd

include hζ d hd in
theorem sourceKPCuspProductHeightMeasure_compact_lt_top
    (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
    (hpos : ∀ y ∈ B, ∀ v, 0 < y v) : sourceKPCuspProductHeightMeasure K B < ⊤ := by
  obtain ⟨c,hc,hm⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ d hd
  have hmap := sourceKPCuspProductCoordinates_map_restrict_unitCell K hζ d hd c hm B hB.measurableSet
  have hmass := congrArg
    (fun μ : Measure ((I → ℝ) × (V → ℝ)) => μ Set.univ) hmap
  have hcell : unitTorusUnitCellMeasure I Set.univ = 1 := by
    rw [unitTorusUnitCellMeasure,Measure.pi_univ]
    simp
  have htotal : ((unitTorusUnitCellMeasure I).prod
      ((sourceKPCuspProductHeightMeasure K).restrict B)) Set.univ =
      sourceKPCuspProductHeightMeasure K B := by
    rw [← Set.univ_prod_univ,Measure.prod_prod,hcell,Measure.restrict_apply_univ,one_mul]
  have hmass' : productVolume V (sourceKPCuspNativeBand K hζ d hd B) =
      (c : ℝ≥0∞) * sourceKPCuspProductHeightMeasure K B := by
    rw [Measure.map_apply (E).symm.continuous.measurable MeasurableSet.univ,
      Set.preimage_univ,Measure.restrict_apply_univ,Measure.smul_apply,smul_eq_mul] at hmass
    change productVolume V (sourceKPCuspNativeBand K hζ d hd B) =
      (c : ℝ≥0∞) * ((unitTorusUnitCellMeasure I).prod
        ((sourceKPCuspProductHeightMeasure K).restrict B)) Set.univ at hmass
    rw [htotal] at hmass
    exact hmass
  have hsub : sourceKPCuspNativeBand K hζ d hd B ⊆
      sourceKPCuspNativeCompactBox K hζ d hd B := by
    intro p hp
    refine ⟨(E).symm p,⟨?_,hp.2⟩,(E).apply_symm_apply p⟩
    exact ⟨fun i => (hp.1 i (Set.mem_univ i)).1.le,
      fun i => (hp.1 i (Set.mem_univ i)).2⟩
  have hfinite : productVolume V (sourceKPCuspNativeBand K hζ d hd B) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub)
      (productVolume_compact_lt_top
        (sourceKPCuspNativeCompactBox_isCompact K hζ d hd B hB)
        (sourceKPCuspNativeCompactBox_positive K hζ d hd B hpos))
  apply lt_top_iff_ne_top.mpr
  intro htop
  rw [hmass',htop,ENNReal.mul_top (by exact_mod_cast hc.ne')] at hfinite
  exact (lt_irrefl ⊤) hfinite

end
end ArtinMatthews
