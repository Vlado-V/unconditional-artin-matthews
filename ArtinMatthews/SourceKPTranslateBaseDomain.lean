module

public import ArtinMatthews.SourceKPAutomorphicMeasureChoice
public import ArtinMatthews.SourceKPCuspFundamentalSection
public import Mathlib.MeasureTheory.Measure.Count


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine measurable rational fundamental domain assembled from the actual
archimedean arithmetic components. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Set Topology
open scoped NumberField MatrixGroups AdeleRing Pointwise ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "A" => PGL(2, InfiniteAdeleRing K)
local notation "Γ" => PGL(2, K)
local notation "F" => SourceKPFiniteLevelFiber K hζ
local notation "X" => SourceKPFiniteLevelSpace K hζ
local notation "I" => SourceKPFiniteOrbit K hζ
local notation "b" => sourceKPFiniteOrbitRepresentative K hζ
local notation "r" => sourceKPRationalArchMap K hζ

def sourceKPTranslateBaseSlice (i : I) : Set A :=
  sourceKPArchComponentFundamentalDomain K hζ (b i) Measure.count

theorem sourceKPTranslateBaseSlice_measurable (i : I) :
    MeasurableSet (sourceKPTranslateBaseSlice K hζ i) :=
  sourceKPArchComponentFundamentalDomain_measurable K hζ (b i) Measure.count

theorem sourceKPTranslateBaseSlice_existsUnique (i : I) (a : A) :
    ∃! δ : sourceKPArchComponentSubgroup K hζ (b i),
      δ • a ∈ sourceKPTranslateBaseSlice K hζ i := by
  let D := sourceKPTranslateBaseSlice K hζ i
  have hD : IsFundamentalDomain (sourceKPArchComponentSubgroup K hζ (b i)) D Measure.count :=
    sourceKPArchComponentFundamentalDomain_isFundamental K hζ (b i) Measure.count
  obtain ⟨δ,hδ⟩ := Measure.ae_count_iff.mp hD.ae_covers a
  refine ⟨δ,hδ,?_⟩
  intro ε hε
  by_contra hne
  have hd := hD.aedisjoint (inv_injective.ne hne)
  have he : ε⁻¹ • D ∩ δ⁻¹ • D = ∅ := Measure.count_eq_zero_iff.mp hd
  have ha : a ∈ ε⁻¹ • D ∩ δ⁻¹ • D := ⟨by
    simpa only [mem_smul_set_iff_inv_smul_mem, inv_inv] using hε, by
    simpa only [mem_smul_set_iff_inv_smul_mem, inv_inv] using hδ⟩
  simpa only [he, notMem_empty] using ha

theorem sourceKPTranslateBaseSlice_isFundamental (i : I) (ν : Measure A) :
    IsFundamentalDomain (sourceKPArchComponentSubgroup K hζ (b i))
      (sourceKPTranslateBaseSlice K hζ i) ν :=
  IsFundamentalDomain.mk' (sourceKPTranslateBaseSlice_measurable K hζ i).nullMeasurableSet
    (sourceKPTranslateBaseSlice_existsUnique K hζ i)

def sourceKPTranslateBaseDomain : Set X :=
  ⋃ i : I, Prod.snd ⁻¹' ({b i} : Set F) ∩ Prod.fst ⁻¹' sourceKPTranslateBaseSlice K hζ i

theorem sourceKPTranslateBaseDomain_mem (x : X) :
    x ∈ sourceKPTranslateBaseDomain K hζ ↔
      ∃ i : I, x.2 = b i ∧ x.1 ∈ sourceKPTranslateBaseSlice K hζ i := by
  simp only [sourceKPTranslateBaseDomain, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]

theorem sourceKPTranslateBaseDomain_measurable :
    MeasurableSet (sourceKPTranslateBaseDomain K hζ) := by
  apply MeasurableSet.iUnion
  intro i
  exact ((measurableSet_singleton (b i)).preimage measurable_snd).inter
    ((sourceKPTranslateBaseSlice_measurable K hζ i).preimage measurable_fst)

theorem sourceKPTranslateBaseDomain_existsUnique (x : X) :
    ∃! γ : Γ, γ • x ∈ sourceKPTranslateBaseDomain K hζ := by
  let i := sourceKPFiniteOrbitMk K hζ x.2
  let c := b i
  have hi : sourceKPFiniteOrbitMk K hζ c = sourceKPFiniteOrbitMk K hζ x.2 :=
    sourceKPFiniteOrbitRepresentative_spec K hζ i
  obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hi)
  let a := r γ * x.1
  obtain ⟨δ,hδ,huniq⟩ := sourceKPTranslateBaseSlice_existsUnique K hζ i a
  obtain ⟨ε,hε,hεδ⟩ := δ.prop
  refine ⟨ε * γ, ?_, ?_⟩
  · apply (sourceKPTranslateBaseDomain_mem K hζ _).mpr
    refine ⟨i, ?_, ?_⟩
    · change (ε * γ) • x.2 = c
      rw [mul_smul, hγ]
      exact hε
    · change r (ε * γ) * x.1 ∈ sourceKPTranslateBaseSlice K hζ i
      rw [map_mul, mul_assoc, hεδ]
      exact hδ
  · intro η hη
    obtain ⟨j,hηfin,hηarch⟩ := (sourceKPTranslateBaseDomain_mem K hζ _).mp hη
    change η • x.2 = b j at hηfin
    change r η * x.1 ∈ sourceKPTranslateBaseSlice K hζ j at hηarch
    have horb : sourceKPFiniteOrbitMk K hζ (η • x.2) = i :=
      Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨η,rfl⟩)
    rw [hηfin, sourceKPFiniteOrbitRepresentative_spec] at horb
    subst j
    have hfix : η * γ⁻¹ ∈ sourceKPRationalFiniteStabilizer K hζ c := by
      change (η * γ⁻¹) • c = c
      calc
        _ = η • x.2 := by rw [← hγ, mul_smul, inv_smul_smul]
        _ = _ := hηfin
    let δ' : sourceKPArchComponentSubgroup K hζ c :=
      ⟨r (η * γ⁻¹), ⟨η * γ⁻¹,hfix,rfl⟩⟩
    have hδ' : δ' • a ∈ sourceKPTranslateBaseSlice K hζ i := by
      change r (η * γ⁻¹) * (r γ * x.1) ∈ sourceKPTranslateBaseSlice K hζ i
      rw [map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
      exact hηarch
    have he : r (η * γ⁻¹) = r ε :=
      (congrArg Subtype.val (huniq δ' hδ')).trans hεδ.symm
    have he' := sourceKPCuspRationalArchMap_injective K hζ he
    simpa only [inv_mul_cancel_right] using congrArg (· * γ) he'

theorem sourceKPTranslateBaseDomain_isFundamental (ν : Measure X) :
    IsFundamentalDomain Γ (sourceKPTranslateBaseDomain K hζ) ν :=
  IsFundamentalDomain.mk' (sourceKPTranslateBaseDomain_measurable K hζ).nullMeasurableSet
    (sourceKPTranslateBaseDomain_existsUnique K hζ)

end
end ArtinMatthews
