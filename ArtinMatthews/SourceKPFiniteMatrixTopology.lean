module

public import ArtinMatthews.SourceKPFiniteUnitTopology
public import ArtinMatthews.SourceKPIntegralMatrixValuation
public import ArtinMatthews.SourceKPDeepCongruenceTopology


set_option backward.privateInPublic true
@[expose] public section

/-! Compact-open finite adelic matrix groups, with deep conditions only at wild places. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]
local notation "Pr" => HeightOneSpectrum (𝓞 K)

def sourceKPFiniteIntegralMatrixGroup : Subgroup (GL (Fin 2) 𝔸ᶠ[K]) :=
  ((sourceKPIntegralFiniteRing K).matrix).toSubmonoid.units

lemma sourceKPFiniteIntegralMatrixGroup_isCompact :
    IsCompact (sourceKPFiniteIntegralMatrixGroup K : Set (GL (Fin 2) 𝔸ᶠ[K])) :=
  Submonoid.units_isCompact (sourceKPIntegralFiniteRing_isCompact K).matrix

lemma sourceKPFiniteIntegralMatrixGroup_isOpen :
    IsOpen (sourceKPFiniteIntegralMatrixGroup K : Set (GL (Fin 2) 𝔸ᶠ[K])) :=
  Submonoid.isOpen_units (sourceKPIntegralFiniteRing_isOpen K).matrix

lemma sourceKPFiniteIntegralMatrixGroup_mem (g : GL (Fin 2) 𝔸ᶠ[K]) :
    g ∈ sourceKPFiniteIntegralMatrixGroup K ↔
      ∀ P : Pr, SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceKPAdeleMatrixAt K P g) := by
  constructor
  · intro hg P
    apply (sourceKPIntegralMatrixMap_mem_range K P _).mp
    rw [sourceKPIntegralMatrixMap_range]
    exact ⟨fun i j => (sourceKPIntegralFiniteRing_mem K _).mp (hg.1 i j) P,
      fun i j => (sourceKPIntegralFiniteRing_mem K _).mp (hg.2 i j) P⟩
  · intro hg
    have hl (P : Pr) : sourceKPAdeleMatrixAt K P g ∈
        (sourceKPIntegralMatrixRing K P).toSubmonoid.units := by
      exact (Set.ext_iff.mp (sourceKPIntegralMatrixMap_range K P) _).mp
        ((sourceKPIntegralMatrixMap_mem_range K P _).mpr (hg P))
    exact ⟨fun i j => (sourceKPIntegralFiniteRing_mem K _).mpr (fun P => (hl P).1 i j),
      fun i j => (sourceKPIntegralFiniteRing_mem K _).mpr (fun P => (hl P).2 i j)⟩

lemma sourceKPAdeleMatrixAt_continuous (P : Pr) : Continuous (sourceKPAdeleMatrixAt K P) :=
  (RestrictedProduct.continuous_eval P).generalLinearGroup_map

def sourceKPFiniteDeepMatrixGroup : Subgroup (GL (Fin 2) 𝔸ᶠ[K]) where
  carrier := {g | g ∈ sourceKPFiniteIntegralMatrixGroup K ∧
    ∀ P ∈ sixthWildPrimes K, sourceKPAdeleMatrixAt K P g ∈ (sourceKPDeepLocalBase K P).range}
  one_mem' := by
    refine ⟨(sourceKPFiniteIntegralMatrixGroup K).one_mem, ?_⟩
    intro P _
    rw [map_one]
    exact (sourceKPDeepLocalBase K P).range.one_mem
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨(sourceKPFiniteIntegralMatrixGroup K).mul_mem hg hh, ?_⟩
    intro P hP
    rw [map_mul]
    exact (sourceKPDeepLocalBase K P).range.mul_mem (hg' P hP) (hh' P hP)
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨(sourceKPFiniteIntegralMatrixGroup K).inv_mem hg, ?_⟩
    intro P hP
    rw [map_inv]
    exact (sourceKPDeepLocalBase K P).range.inv_mem (hg' P hP)

lemma sourceKPFiniteDeepMatrixGroup_set :
    (sourceKPFiniteDeepMatrixGroup K : Set (GL (Fin 2) 𝔸ᶠ[K])) =
      (sourceKPFiniteIntegralMatrixGroup K : Set (GL (Fin 2) 𝔸ᶠ[K])) ∩
        ⋂ P ∈ sixthWildPrimes K,
          (sourceKPAdeleMatrixAt K P) ⁻¹' ((sourceKPDeepLocalBase K P).range : Set (GL (Fin 2) (P.adicCompletion K))) := by
  ext g
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  rfl

lemma sourceKPFiniteDeepMatrixGroup_isOpen :
    IsOpen (sourceKPFiniteDeepMatrixGroup K : Set (GL (Fin 2) 𝔸ᶠ[K])) := by
  rw [sourceKPFiniteDeepMatrixGroup_set]
  exact (sourceKPFiniteIntegralMatrixGroup_isOpen K).inter (isOpen_biInter_finset fun P _ =>
    (sourceKPDeepLocalBase_range_isOpen K P).preimage (sourceKPAdeleMatrixAt_continuous K P))

lemma sourceKPFiniteDeepMatrixGroup_isCompact :
    IsCompact (sourceKPFiniteDeepMatrixGroup K : Set (GL (Fin 2) 𝔸ᶠ[K])) := by
  rw [sourceKPFiniteDeepMatrixGroup_set]
  exact (sourceKPFiniteIntegralMatrixGroup_isCompact K).inter_right
    (isClosed_iInter fun P => isClosed_iInter fun _ =>
      (sourceKPDeepLocalBase_range_isCompact K P).isClosed.preimage
        (sourceKPAdeleMatrixAt_continuous K P))

lemma sourceKPFiniteDeepMatrixGroup_mem (g : GL (Fin 2) 𝔸ᶠ[K]) :
    g ∈ sourceKPFiniteDeepMatrixGroup K ↔
      (∀ P : Pr, SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceKPAdeleMatrixAt K P g)) ∧
        ∀ P : Pr, (6 : 𝓞 K) ∈ P.asIdeal →
          sourceKPAdeleMatrixAt K P g ∈ (sourceKPDeepLocalBase K P).range := by
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [sourceKPFiniteIntegralMatrixGroup_mem]
  simp only [mem_sixthWildPrimes]

end
end ArtinMatthews
