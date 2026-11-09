module

public import ArtinMatthews.SourceKPLocalUnitTopology
public import Mathlib.Topology.Algebra.Group.Matrix


set_option backward.privateInPublic true
@[expose] public section

/-! Compact-open integral matrix groups in the completed local fields. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology Matrix
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "O" => P.adicCompletionIntegers K

def sourceKPIntegralMatrixRing : Subring (Matrix (Fin 2) (Fin 2) L) :=
  (P.adicCompletionIntegers K).toSubring.matrix

lemma sourceKPIntegralMatrixRing_isCompact :
    IsCompact (sourceKPIntegralMatrixRing K P : Set (Matrix (Fin 2) (Fin 2) L)) :=
  (sourceKPLocalIntegers_isCompact K P).matrix

lemma sourceKPIntegralMatrixRing_isOpen :
    IsOpen (sourceKPIntegralMatrixRing K P : Set (Matrix (Fin 2) (Fin 2) L)) :=
  (sourceKPLocalIntegers_isOpen K P).matrix

def sourceKPIntegralMatrixMap : GL (Fin 2) O →* GL (Fin 2) L :=
  GeneralLinearGroup.map (algebraMap O L)

lemma sourceKPIntegralMatrixMap_continuous : Continuous (sourceKPIntegralMatrixMap K P) :=
  (continuous_subtype_val : Continuous (fun a : O => (a : L))).generalLinearGroup_map

lemma sourceKPIntegralMatrixMap_range :
    Set.range (sourceKPIntegralMatrixMap K P) =
      ((sourceKPIntegralMatrixRing K P).toSubmonoid.units : Set (GL (Fin 2) L)) := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨fun i j => (a.val i j).property, fun i j => (a.inv i j).property⟩
  · intro hg
    let A : Matrix (Fin 2) (Fin 2) O := fun i j => ⟨g.val i j, hg.1 i j⟩
    let B : Matrix (Fin 2) (Fin 2) O := fun i j => ⟨g.inv i j, hg.2 i j⟩
    have hinj : Function.Injective (RingHom.mapMatrix (algebraMap O L) :
        Matrix (Fin 2) (Fin 2) O → Matrix (Fin 2) (Fin 2) L) := by
      intro a b h
      apply Matrix.ext
      intro i j
      exact Subtype.ext (congrFun (congrFun h i) j)
    have hAB : A * B = 1 := by
      apply hinj
      rw [map_mul, map_one]
      exact g.val_inv
    have hBA : B * A = 1 := by
      apply hinj
      rw [map_mul, map_one]
      exact g.inv_val
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    apply Units.ext
    rfl

lemma sourceKPIntegralMatrixMap_isOpenEmbedding :
    IsOpenEmbedding (sourceKPIntegralMatrixMap K P) := by
  refine ⟨?_, ?_⟩
  · exact (Topology.IsEmbedding.subtypeVal :
      IsEmbedding (fun a : O => (a : L))).generalLinearGroup_map
  · rw [sourceKPIntegralMatrixMap_range]
    exact Submonoid.isOpen_units (sourceKPIntegralMatrixRing_isOpen K P)

lemma sourceKPIntegralMatrixGroup_isCompact :
    IsCompact (Set.range (sourceKPIntegralMatrixMap K P)) := by
  rw [sourceKPIntegralMatrixMap_range]
  exact Submonoid.units_isCompact (sourceKPIntegralMatrixRing_isCompact K P)

lemma sourceKPIntegralMatrixGroup_isOpen :
    IsOpen (Set.range (sourceKPIntegralMatrixMap K P)) :=
  (sourceKPIntegralMatrixMap_isOpenEmbedding K P).isOpen_range

end
end ArtinMatthews
