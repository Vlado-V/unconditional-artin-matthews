module

public import ArtinMatthews.SourceKPGlobalChartMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! The exact scalar L2 lift from the global automorphic quotient chart. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

def sourceKPFiniteChartLocalMeasure : Measure (sourceKPUpperFiniteChart K hζ b p).domain :=
  (Nat.card (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p) : ℝ≥0∞)⁻¹ •
    sourceFiniteChartDomainMeasure (sourceKPUpperFiniteChart K hζ b p) (sourceKPArchHyperbolicMeasure K)

def sourceKPFiniteChartQuotientMeasure : Measure (SourceKPAutomorphicCompactLevel K hζ) :=
  (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)).restrict
    (Set.range (sourceKPFiniteChartProjection K hζ b p))

theorem sourceKPFiniteChartProjection_measured :
    MeasurePreserving (sourceKPFiniteChartProjection K hζ b p)
      (sourceKPFiniteChartLocalMeasure K hζ b p) (sourceKPFiniteChartQuotientMeasure K hζ b p) :=
  sourceKPFiniteChartProjection_measurePreserving K hζ b p

abbrev SourceKPFiniteChartQuotientL2 := Lp ℂ 2 (sourceKPFiniteChartQuotientMeasure K hζ b p)
abbrev SourceKPFiniteChartLiftedL2 := Lp ℂ 2 (sourceKPFiniteChartLocalMeasure K hζ b p)

def sourceKPFiniteChartL2Pullback :
    SourceKPFiniteChartQuotientL2 K hζ b p →ₗᵢ[ℂ] SourceKPFiniteChartLiftedL2 K hζ b p :=
  Lp.compMeasurePreservingₗᵢ ℂ (sourceKPFiniteChartProjection K hζ b p)
    (sourceKPFiniteChartProjection_measured K hζ b p)

theorem sourceKPFiniteChartL2Pullback_coe (f : SourceKPFiniteChartQuotientL2 K hζ b p) :
    (sourceKPFiniteChartL2Pullback K hζ b p f : (sourceKPUpperFiniteChart K hζ b p).domain → ℂ)
      =ᵐ[sourceKPFiniteChartLocalMeasure K hζ b p]
        fun x => f (sourceKPFiniteChartProjection K hζ b p x) :=
  Lp.coeFn_compMeasurePreserving f (sourceKPFiniteChartProjection_measured K hζ b p)

theorem sourceKPFiniteChartL2Pullback_norm (f : SourceKPFiniteChartQuotientL2 K hζ b p) :
    ‖sourceKPFiniteChartL2Pullback K hζ b p f‖ = ‖f‖ :=
  (sourceKPFiniteChartL2Pullback K hζ b p).norm_map f

theorem sourceKPFiniteChartL2Pullback_injective :
    Function.Injective (sourceKPFiniteChartL2Pullback K hζ b p) :=
  (sourceKPFiniteChartL2Pullback K hζ b p).injective

theorem sourceKPFiniteChartLocalMeasure_weight :
    0 < (Nat.card (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p) : ℝ≥0∞)⁻¹ ∧
      (Nat.card (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p) : ℝ≥0∞)⁻¹ ≠ ⊤ :=
  sourceFiniteChart_weight_pos (sourceKPUpperFiniteChart K hζ b p)

end
end ArtinMatthews
