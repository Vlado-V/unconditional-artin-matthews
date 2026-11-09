module

public import ArtinMatthews.SourceKPFiniteChartCoordinateMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! The exact complex-valued finite-isotropy chart integration formula. -/

namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology Classical ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFiniteChart_complex_integral
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)
    (F : SourceKPAutomorphicCompactLevel K hζ → ℂ) (hF : Measurable F) :
    (∫ x in sourceKPFiniteChartCoordinateDomain K hζ b p,
      F (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x))
        ∂productVolume (InfinitePlace K)) =
      (Nat.card (SourceKPFiniteChartStabilizer K hζ b p) : ℂ) *
        ∫ y in Set.range (sourceKPFiniteChartProjection K hζ b p), F y
          ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ) := by
  let c := sourceKPUpperFiniteChart K hζ b p
  let μD := sourceFiniteChartDomainMeasure c (sourceKPArchHyperbolicMeasure K)
  let π := sourceKPFiniteChartProjection K hζ b p
  let n := Nat.card (SourceKPFiniteChartStabilizer K hζ b p)
  let L : ProductSpace (InfinitePlace K) → ℂ :=
    fun x => F (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x))
  have hL : Measurable L := hF.comp
    ((sourceKPUpperToCompact_continuous K hζ b).measurable.comp
      (sourceKPArchEuclideanUpperMap_preserving K).measurable)
  have hcoord : (∫ x in sourceKPFiniteChartCoordinateDomain K hζ b p,
      L x ∂productVolume (InfinitePlace K)) = ∫ x : c.domain, F (π x) ∂μD := by
    have hm := sourceKPFiniteChartCoordinates_measurePreserving K hζ b p
    calc
      _ = ∫ x, L x ∂Measure.map
          (fun x : c.domain => sourceKPArchUpperEuclideanMap K x.val) μD := by rw [hm.map_eq]
      _ = ∫ x : c.domain, L (sourceKPArchUpperEuclideanMap K x.val) ∂μD :=
        integral_map hm.measurable.aemeasurable hL.aestronglyMeasurable
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [L, π, sourceKPFiniteChartProjection]
        rw [sourceKPArchUpperEuclideanMap_left_inverse]
  have hquot : (∫ y in Set.range π, F y
      ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) =
      (n : ℂ)⁻¹ * ∫ x : c.domain, F (π x) ∂μD := by
    have hm := sourceKPFiniteChartProjection_measurePreserving K hζ b p
    calc
      _ = ∫ y, F y ∂Measure.map π ((n : ℝ≥0∞)⁻¹ • μD) := by rw [hm.map_eq]
      _ = ∫ x : c.domain, F (π x) ∂((n : ℝ≥0∞)⁻¹ • μD) :=
        integral_map hm.measurable.aemeasurable hF.aestronglyMeasurable
      _ = _ := by
        rw [integral_smul_measure]
        simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul,
          Complex.ofReal_inv, Complex.ofReal_natCast]
  have hn : (n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos.ne' : Nat.card (SourceKPFiniteChartStabilizer K hζ b p) ≠ 0)
  change (∫ x in sourceKPFiniteChartCoordinateDomain K hζ b p,
    L x ∂productVolume (InfinitePlace K)) = (n : ℂ) * _
  rw [hcoord,hquot,← mul_assoc,mul_inv_cancel₀ hn,one_mul]

end
end ArtinMatthews
