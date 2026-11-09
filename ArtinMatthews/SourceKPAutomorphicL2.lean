module

public import ArtinMatthews.SourceKPAutomorphicMeasure
public import ArtinMatthews.SourceKPArchDoubleQuotient
public import Mathlib.MeasureTheory.Function.L2Space


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPAutomorphicCompactLevel_measurableSpace :
    MeasurableSpace (SourceKPAutomorphicCompactLevel K hζ) := borel _

instance sourceKPAutomorphicCompactLevel_borelSpace :
    BorelSpace (SourceKPAutomorphicCompactLevel K hζ) := ⟨rfl⟩

theorem sourceKPAutomorphicCompactMk_measurable : Measurable (sourceKPAutomorphicCompactMk K hζ) :=
  (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).continuous.measurable

def sourceKPAutomorphicCompactMeasure (μ : Measure (PGL(2, InfiniteAdeleRing K))) :
    Measure (SourceKPAutomorphicCompactLevel K hζ) :=
  Measure.map (sourceKPAutomorphicCompactMk K hζ) (sourceKPAutomorphicMeasure K hζ μ)

theorem sourceKPAutomorphicCompactMk_measurePreserving
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) :
    MeasurePreserving (sourceKPAutomorphicCompactMk K hζ)
      (sourceKPAutomorphicMeasure K hζ μ) (sourceKPAutomorphicCompactMeasure K hζ μ) :=
  ⟨sourceKPAutomorphicCompactMk_measurable K hζ,rfl⟩

abbrev SourceKPAutomorphicL2 (μ : Measure (PGL(2, InfiniteAdeleRing K))) :=
  Lp ℂ 2 (sourceKPAutomorphicCompactMeasure K hζ μ)

def sourceKPAutomorphicL2Pullback (μ : Measure (PGL(2, InfiniteAdeleRing K))) :
    SourceKPAutomorphicL2 K hζ μ →ₗᵢ[ℂ] Lp ℂ 2 (sourceKPAutomorphicMeasure K hζ μ) :=
  Lp.compMeasurePreservingₗᵢ ℂ (sourceKPAutomorphicCompactMk K hζ)
    (sourceKPAutomorphicCompactMk_measurePreserving K hζ μ)

theorem sourceKPAutomorphicL2Pullback_norm (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    (f : SourceKPAutomorphicL2 K hζ μ) : ‖sourceKPAutomorphicL2Pullback K hζ μ f‖ = ‖f‖ :=
  (sourceKPAutomorphicL2Pullback K hζ μ).norm_map f

end
end ArtinMatthews
