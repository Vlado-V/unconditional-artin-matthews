module

public import ArtinMatthews.SourceKPArchMeasureTopology
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace


set_option backward.privateInPublic true
@[expose] public section

/-! The actual arithmetic component has the Borel measurable quotient structure. -/
namespace ArtinMatthews
open NumberField Matrix Filter Topology
open scoped NumberField MatrixGroups AdeleRing Uniformity
noncomputable section

variable (K : Type) [Field K] [NumberField K]

instance sourceKPArchComponentGroup_polish : PolishSpace (PGL(2, InfiniteAdeleRing K)) := by
  let G := PGL(2, InfiniteAdeleRing K)
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsRightUniformGroup G := { uniformity_eq := rfl }
  have : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace G
  have : (𝓤 G).IsCountablyGenerated := by
    change (Filter.comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 (1 : G))).IsCountablyGenerated
    infer_instance
  exact (inferInstance : PolishSpace G)

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (b : SourceKPFiniteLevelFiber K hζ)

instance sourceKPArchComponentQuotient_t2 : T2Space (SourceKPArchComponentQuotient K hζ b) := by
  have : ProperSMul (sourceKPArchComponentSubgroup K hζ b) (PGL(2, InfiniteAdeleRing K)) :=
    properlyDiscontinuousSMul_iff_properSMul.mp inferInstance
  change T2Space (Quotient (MulAction.orbitRel (sourceKPArchComponentSubgroup K hζ b)
    (PGL(2, InfiniteAdeleRing K))))
  infer_instance

instance sourceKPArchComponentQuotient_secondCountable :
    SecondCountableTopology (SourceKPArchComponentQuotient K hζ b) :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    (show IsOpenQuotientMap (Quotient.mk
      (QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ b))) from
        MulAction.isOpenQuotientMap_quotientMk)

instance sourceKPArchComponentQuotient_borel : BorelSpace (SourceKPArchComponentQuotient K hζ b) := by
  have : SecondCountableTopology (Quotient (MulAction.orbitRel
      (sourceKPArchComponentSubgroup K hζ b) (PGL(2, InfiniteAdeleRing K)))) :=
    sourceKPArchComponentQuotient_secondCountable K hζ b
  have : T2Space (Quotient (MulAction.orbitRel
      (sourceKPArchComponentSubgroup K hζ b) (PGL(2, InfiniteAdeleRing K)))) :=
    sourceKPArchComponentQuotient_t2 K hζ b
  change BorelSpace (Quotient (MulAction.orbitRel (sourceKPArchComponentSubgroup K hζ b)
    (PGL(2, InfiniteAdeleRing K))))
  exact Quotient.borelSpace

end
end ArtinMatthews
