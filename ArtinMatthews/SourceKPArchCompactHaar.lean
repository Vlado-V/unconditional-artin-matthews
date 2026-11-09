module

public import ArtinMatthews.SourceKPArchCompactOrbifold
public import ArtinMatthews.SourceKPArchMeasureTopology
public import Mathlib.MeasureTheory.Measure.Haar.Unique


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Topology TopologicalSpace MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPArchCompactGroup_compactSpace :
    CompactSpace (sourceKPArchBaseCompactSubgroup K hζ) :=
  isCompact_iff_compactSpace.mp (sourceKPArchBaseCompactSubgroup_isCompact K hζ)

def sourceKPArchCompactPositive : PositiveCompacts (sourceKPArchBaseCompactSubgroup K hζ) :=
  ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩

def sourceKPArchCompactHaar : Measure (sourceKPArchBaseCompactSubgroup K hζ) :=
  Measure.haarMeasure (sourceKPArchCompactPositive K hζ)

instance sourceKPArchCompactHaar_isHaar : (sourceKPArchCompactHaar K hζ).IsHaarMeasure := by
  unfold sourceKPArchCompactHaar
  infer_instance

theorem sourceKPArchCompactHaar_univ : sourceKPArchCompactHaar K hζ Set.univ = 1 := by
  exact Measure.haarMeasure_self

instance sourceKPArchCompactHaar_isProbability : IsProbabilityMeasure (sourceKPArchCompactHaar K hζ) :=
  ⟨sourceKPArchCompactHaar_univ K hζ⟩

instance sourceKPArchCompactHaar_rightInvariant : (sourceKPArchCompactHaar K hζ).IsMulRightInvariant := by
  constructor
  intro k
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure
    (Measure.map (fun h : sourceKPArchBaseCompactSubgroup K hζ => h*k)
      (sourceKPArchCompactHaar K hζ)) (sourceKPArchCompactHaar K hζ)

end
end ArtinMatthews
