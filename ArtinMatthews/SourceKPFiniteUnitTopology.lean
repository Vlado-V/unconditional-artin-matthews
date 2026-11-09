module

public import ArtinMatthews.SourceKPLocalUnitTopology


set_option backward.privateInPublic true
@[expose] public section

/-! The compact-open finite unit subgroup in the standard restricted-product topology. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain SourcePhysical Topology
open scoped NumberField AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "L" => fun P : HeightOneSpectrum (𝓞 K) => HeightOneSpectrum.adicCompletion K P
local notation "O" => fun P : HeightOneSpectrum (𝓞 K) => HeightOneSpectrum.adicCompletionIntegers K P

instance sourceKPFiniteAdeleT2Space : T2Space 𝔸ᶠ[K] :=
  inferInstanceAs (T2Space (RestrictedProduct L (fun P => (O P : Set (L P))) Filter.cofinite))

def sourceKPIntegralFiniteMap : (∀ P : Pr, O P) →+* 𝔸ᶠ[K] where
  toFun := RestrictedProduct.structureMap L (fun P => (O P : Set (L P))) Filter.cofinite
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def sourceKPIntegralFiniteRing : Subring 𝔸ᶠ[K] := (sourceKPIntegralFiniteMap K).range

lemma sourceKPIntegralFiniteRing_mem (a : 𝔸ᶠ[K]) :
    a ∈ sourceKPIntegralFiniteRing K ↔ ∀ P : Pr, a P ∈ O P := by
  change a ∈ Set.range (RestrictedProduct.structureMap L (fun P => (O P : Set (L P))) Filter.cofinite) ↔ _
  rw [RestrictedProduct.range_structureMap]
  rfl

lemma sourceKPIntegralFiniteRing_isCompact : IsCompact (sourceKPIntegralFiniteRing K : Set 𝔸ᶠ[K]) := by
  let : ∀ P : Pr, CompactSpace (O P) := fun P =>
    isCompact_iff_compactSpace.mp (sourceKPLocalIntegers_isCompact K P)
  change IsCompact (Set.range (RestrictedProduct.structureMap L (fun P => (O P : Set (L P))) Filter.cofinite))
  exact isCompact_range (RestrictedProduct.isEmbedding_structureMap.continuous)

lemma sourceKPIntegralFiniteRing_isOpen : IsOpen (sourceKPIntegralFiniteRing K : Set 𝔸ᶠ[K]) := by
  change IsOpen (Set.range (RestrictedProduct.structureMap L (fun P => (O P : Set (L P))) Filter.cofinite))
  exact (RestrictedProduct.isOpenEmbedding_structureMap
    (fun P => sourceKPLocalIntegers_isOpen K P)).isOpen_range

def sourceKPFiniteCoordinate (P : Pr) : (𝔸ᶠ[K])ˣ →* (L P)ˣ :=
  Units.map (sourceKPAdeleEval K P).toMonoidHom

lemma sourceKPFiniteCoordinate_continuous (P : Pr) : Continuous (sourceKPFiniteCoordinate K P) :=
  (RestrictedProduct.continuous_eval P).units_map _

def sourceKPIntegralFiniteUnits : Subgroup (𝔸ᶠ[K])ˣ := (sourceKPIntegralFiniteRing K).toSubmonoid.units

lemma sourceKPIntegralFiniteUnits_mem (a : (𝔸ᶠ[K])ˣ) :
    a ∈ sourceKPIntegralFiniteUnits K ↔
      ∀ P : Pr, sourceKPFiniteVal K P (sourceKPFiniteCoordinate K P a : L P) = 1 := by
  constructor
  · intro ha P
    have h1 := (sourceKPIntegralFiniteRing_mem K (a : 𝔸ᶠ[K])).mp ha.1
    have h2 := (sourceKPIntegralFiniteRing_mem K (a⁻¹ : (𝔸ᶠ[K])ˣ)).mp ha.2
    apply (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (K := K) (v := P)).mp
    exact ⟨h1 P, h2 P⟩
  · intro ha
    have hp (P : Pr) : sourceKPFiniteCoordinate K P a ∈ (O P).units :=
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (K := K) (v := P)).mpr (ha P)
    exact ⟨(sourceKPIntegralFiniteRing_mem K _).mpr (fun P => (hp P).1),
      (sourceKPIntegralFiniteRing_mem K _).mpr (fun P => (hp P).2)⟩

lemma sourceKPIntegralFiniteUnits_isCompact : IsCompact (sourceKPIntegralFiniteUnits K : Set (𝔸ᶠ[K])ˣ) :=
  Submonoid.units_isCompact (sourceKPIntegralFiniteRing_isCompact K)

lemma sourceKPIntegralFiniteUnits_isOpen : IsOpen (sourceKPIntegralFiniteUnits K : Set (𝔸ᶠ[K])ˣ) :=
  Submonoid.isOpen_units (sourceKPIntegralFiniteRing_isOpen K)

def sourceKPFiniteUnitSubgroup : Subgroup (𝔸ᶠ[K])ˣ where
  carrier := {a | a ∈ sourceKPIntegralFiniteUnits K ∧
    ∀ P ∈ sixthWildPrimes K, sourceKPFiniteCoordinate K P a ∈ sourceKPLocalCubeUnits K P}
  one_mem' := ⟨(sourceKPIntegralFiniteUnits K).one_mem, by intro P _; rw [map_one]; exact (sourceKPLocalCubeUnits K P).one_mem⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨(sourceKPIntegralFiniteUnits K).mul_mem ha.1 hb.1, ?_⟩
    intro P hP
    rw [map_mul]
    exact (sourceKPLocalCubeUnits K P).mul_mem (ha.2 P hP) (hb.2 P hP)
  inv_mem' := by
    intro a ha
    refine ⟨(sourceKPIntegralFiniteUnits K).inv_mem ha.1, ?_⟩
    intro P hP
    rw [map_inv]
    exact (sourceKPLocalCubeUnits K P).inv_mem (ha.2 P hP)

lemma sourceKPFiniteUnitSubgroup_set :
    (sourceKPFiniteUnitSubgroup K : Set (𝔸ᶠ[K])ˣ) =
      (sourceKPIntegralFiniteUnits K : Set (𝔸ᶠ[K])ˣ) ∩
        ⋂ P ∈ sixthWildPrimes K, (sourceKPFiniteCoordinate K P) ⁻¹' (sourceKPLocalCubeUnits K P : Set (L P)ˣ) := by
  ext a
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  rfl

lemma sourceKPFiniteUnitSubgroup_isOpen : IsOpen (sourceKPFiniteUnitSubgroup K : Set (𝔸ᶠ[K])ˣ) := by
  rw [sourceKPFiniteUnitSubgroup_set]
  exact (sourceKPIntegralFiniteUnits_isOpen K).inter (isOpen_biInter_finset fun P _ =>
    (sourceKPLocalCubeUnits_isOpen K P).preimage (sourceKPFiniteCoordinate_continuous K P))

lemma sourceKPFiniteUnitSubgroup_isCompact : IsCompact (sourceKPFiniteUnitSubgroup K : Set (𝔸ᶠ[K])ˣ) := by
  rw [sourceKPFiniteUnitSubgroup_set]
  exact (sourceKPIntegralFiniteUnits_isCompact K).inter_right
    (isClosed_iInter fun P => isClosed_iInter fun _ =>
      (sourceKPLocalCubeUnits_isCompact K P).isClosed.preimage (sourceKPFiniteCoordinate_continuous K P))

lemma sourceKPFiniteUnitSubgroup_mem (a : (𝔸ᶠ[K])ˣ) :
    a ∈ sourceKPFiniteUnitSubgroup K ↔
      (∀ P : Pr, sourceKPFiniteVal K P (sourceKPFiniteCoordinate K P a : L P) = 1) ∧
      (∀ P : Pr, (6 : 𝓞 K) ∈ P.asIdeal → ∃ b : (L P)ˣ, b^3 = sourceKPFiniteCoordinate K P a) := by
  constructor
  · intro ha
    refine ⟨(sourceKPIntegralFiniteUnits_mem K a).mp ha.1, ?_⟩
    intro P hP
    exact ((sourceKPLocalCubeUnits_mem_iff K P _).mp
      (ha.2 P ((mem_sixthWildPrimes P).mpr hP))).2
  · rintro ⟨ha, hb⟩
    refine ⟨(sourceKPIntegralFiniteUnits_mem K a).mpr ha, ?_⟩
    intro P hP
    exact (sourceKPLocalCubeUnits_mem_iff K P _).mpr
      ⟨ha P, hb P ((mem_sixthWildPrimes P).mp hP)⟩

lemma sourceKPAdelicUnitIdeles_iff (a : IdeleGroup (𝓞 K) K) :
    a ∈ sourceKPAdelicUnitIdeles K ↔
      sourceKPIdeleFiniteUnit K a ∈ sourceKPFiniteUnitSubgroup K ∧
        ∀ w, ‖(sourceKPIdeleInfiniteCoordinate K w a : w.Completion)‖ = 1 := by
  rw [sourceKPFiniteUnitSubgroup_mem]
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _) ∧ _
  tauto

end
end ArtinMatthews
