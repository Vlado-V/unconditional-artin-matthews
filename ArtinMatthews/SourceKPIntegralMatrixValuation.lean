module

public import ArtinMatthews.SourceKPIntegralMatrixTopology
public import ArtinMatthews.SourceKPIntegralGroup


set_option backward.privateInPublic true
@[expose] public section

/-! The topological integral matrix group agrees with the actual valuation predicate. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology Matrix
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "O" => P.adicCompletionIntegers K

lemma sourceKPIntegralMatrixMap_integral (g : GL (Fin 2) O) :
    SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceKPIntegralMatrixMap K P g) := by
  refine ⟨?_, ?_⟩
  · intro i j
    exact (g.val i j).property
  · change sourceKPFiniteVal K P
      (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap O L) g) : L) = 1
    rw [GeneralLinearGroup.map_det]
    change sourceKPFiniteVal K P ((GeneralLinearGroup.det g : O) : L) = 1
    exact (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (K := K) (v := P)).mp (GeneralLinearGroup.det g).isUnit

lemma sourceKPIntegralMatrixMap_mem_range (g : GL (Fin 2) L) :
    g ∈ Set.range (sourceKPIntegralMatrixMap K P) ↔
      SourceKPIntegralMatrix (sourceKPFiniteVal K P) g := by
  constructor
  · rintro ⟨a, rfl⟩
    exact sourceKPIntegralMatrixMap_integral K P a
  · intro hg
    rw [sourceKPIntegralMatrixMap_range]
    exact ⟨hg.entries, (sourceKPIntegralMatrix_inv _ hg).entries⟩

lemma sourceKPIntegralMatrixMap_range_eq :
    Set.range (sourceKPIntegralMatrixMap K P) = (sourceKPIntegralGroup (sourceKPFiniteVal K P) : Set (GL (Fin 2) L)) := by
  ext g
  exact sourceKPIntegralMatrixMap_mem_range K P g

end
end ArtinMatthews
