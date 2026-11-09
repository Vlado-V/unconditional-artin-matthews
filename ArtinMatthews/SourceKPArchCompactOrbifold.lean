module

public import ArtinMatthews.SourceKPArithmeticLocalQuotient
public import ArtinMatthews.SourceKPAdelicBaseCompactTopology


set_option backward.privateInPublic true
@[expose] public section

/-! The compact archimedean subgroup is the projection of the actual full
base compact subgroup. Its arithmetic homogeneous quotients retain finite
isotropy. -/
namespace ArtinMatthews
open NumberField Matrix Topology Filter
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPArchProjectiveMatrixMap : GL (Fin 2) 𝔸[K] →* PGL(2, InfiniteAdeleRing K) :=
  ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (RingHom.fst _ _))

theorem sourceKPArchProjectiveMatrixMap_continuous :
    Continuous (sourceKPArchProjectiveMatrixMap K) :=
  continuous_quot_mk.comp continuous_fst.generalLinearGroup_map

def sourceKPArchBaseCompactSubgroup : Subgroup (PGL(2, InfiniteAdeleRing K)) :=
  (SourceKPAdelicBaseCompactMatrix K hζ).map (sourceKPArchProjectiveMatrixMap K)

theorem sourceKPArchBaseCompactSubgroup_isCompact :
    IsCompact (sourceKPArchBaseCompactSubgroup K hζ : Set (PGL(2, InfiniteAdeleRing K))) := by
  change IsCompact ((sourceKPArchProjectiveMatrixMap K) ''
    (SourceKPAdelicBaseCompactMatrix K hζ : Set (GL (Fin 2) 𝔸[K])))
  exact (SourceKPAdelicBaseCompactMatrix_isCompact K hζ).image
    (sourceKPArchProjectiveMatrixMap_continuous K)

abbrev SourceKPArchSymmetricSpace :=
  PGL(2, InfiniteAdeleRing K) ⧸ sourceKPArchBaseCompactSubgroup K hζ

instance sourceKPArchBaseCompactSubgroup_isClosed :
    IsClosed (sourceKPArchBaseCompactSubgroup K hζ : Set (PGL(2, InfiniteAdeleRing K))) :=
  (sourceKPArchBaseCompactSubgroup_isCompact K hζ).isClosed

instance sourceKPArchSymmetricSpace_t2 : T2Space (SourceKPArchSymmetricSpace K hζ) := by
  infer_instance

instance sourceKPArchSymmetricSpace_locallyCompact :
    LocallyCompactSpace (SourceKPArchSymmetricSpace K hζ) := by
  infer_instance

instance sourceKPArchSymmetricSpace_properlyDiscontinuous
    (b : SourceKPFiniteLevelFiber K hζ) :
    ProperlyDiscontinuousSMul (sourceKPArchComponentSubgroup K hζ b)
      (SourceKPArchSymmetricSpace K hζ) :=
  sourceCompactSubgroup_quotient_properlyDiscontinuous
    (sourceKPArchComponentSubgroup K hζ b) (sourceKPArchBaseCompactSubgroup K hζ)
    (sourceKPArchBaseCompactSubgroup_isCompact K hζ)

theorem sourceKPArchSymmetricSpace_finite_stabilizer
    (b : SourceKPFiniteLevelFiber K hζ) (x : SourceKPArchSymmetricSpace K hζ) :
    (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) x :
      Set (sourceKPArchComponentSubgroup K hζ b)).Finite :=
  ProperlyDiscontinuousSMul.finite_stabilizer x

theorem sourceKPArchSymmetricSpace_disjoint_neighborhood
    (b : SourceKPFiniteLevelFiber K hζ) (x : SourceKPArchSymmetricSpace K hζ) :
    ∃ U ∈ 𝓝 x, ∀ γ : sourceKPArchComponentSubgroup K hζ b,
      γ • x ≠ x → Disjoint ((γ • ·) '' U) U :=
  sourceKPArchHomogeneous_disjoint_neighborhood K hζ b
    (sourceKPArchBaseCompactSubgroup K hζ)
    (sourceKPArchBaseCompactSubgroup_isCompact K hζ) x

end
end ArtinMatthews
