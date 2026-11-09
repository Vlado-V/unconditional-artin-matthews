module

public import ArtinMatthews.SourceKPTranslateCompactHaar


set_option backward.privateInPublic true
@[expose] public section

/-! Null sets on the compact quotients pull back to the entire representative
spaces. Counting measure in the finite coordinate gives simultaneous almost
everywhere statements for all finite cosets at a fixed archimedean coordinate. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Set Filter
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

private theorem quotient_quasiMeasurePreserving_of_domain
    {Γ X Y : Type*} [Group Γ] [Countable Γ] [MeasurableSpace X] [MeasurableSpace Y]
    [MulAction Γ X] [MeasurableConstSMul Γ X] {ν : Measure X} [SMulInvariantMeasure Γ X ν]
    {E : Set X} (hE : IsFundamentalDomain Γ E ν)
    (q : X → Y) (hq : Measurable q) (hi : ∀ (γ : Γ) x, q (γ • x) = q x) :
    Measure.QuasiMeasurePreserving q ν (Measure.map q (ν.restrict E)) := by
  refine ⟨hq,Measure.AbsolutelyContinuous.mk ?_⟩
  intro S hS hz
  rw [Measure.map_apply hq hS, Measure.restrict_apply (hS.preimage hq)] at hz
  rw [Measure.map_apply hq hS]
  apply hE.measure_zero_of_invariant _ _ hz
  intro γ
  ext x
  rw [mem_smul_set_iff_inv_smul_mem]
  change q (γ⁻¹ • x) ∈ S ↔ q x ∈ S
  rw [hi]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Γ" => PGL(2, K)
local notation "X" => SourceKPFiniteLevelSpace K hζ
local notation "q" => sourceKPFiniteLevelToCompact K hζ
local notation "ν" => sourceKPFiniteRepresentativeHaar K hζ
local notation "μA" => sourceKPArchHaar K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

private theorem baseRational_preserving (γ : Γ) :
    MeasurePreserving (fun x : X => γ • x) ν ν :=
  sourceKPFiniteRepresentativeHaar_left K hζ
    (sourceKPRationalArchMap K hζ γ,sourceKPRationalFiniteMap K hζ γ)

theorem sourceKPFiniteLevelToCompact_full_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving q ν μY := by
  letI : Countable Γ := sourceKPCuspRationalProjective_countable K
  letI : MeasurableConstSMul Γ X := ⟨fun γ => (baseRational_preserving K hζ γ).measurable⟩
  letI : SMulInvariantMeasure Γ X ν := ⟨fun γ S hS => by
    have hm := baseRational_preserving K hζ γ
    rw [← Measure.map_apply hm.measurable hS, hm.map_eq]⟩
  rw [← sourceKPTranslateBaseHaar_map]
  apply quotient_quasiMeasurePreserving_of_domain
    (sourceKPTranslateBaseDomain_isFundamental K hζ ν) q
    (sourceKPFiniteLevelToCompact_measurable K hζ)
  intro γ x
  apply congrArg (sourceKPAutomorphicCompactMk K hζ)
  apply Quotient.sound
  exact MulAction.mem_orbit_iff.mpr ⟨γ,rfl⟩

variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "FJ" => SourceKPTranslateFiniteLevelFiber K hζ T
local notation "XJ" => SourceKPTranslateRepresentativeSpace K hζ T
local notation "qJ" => sourceKPTranslateRepresentativeToCompact K hζ T
local notation "νJ" => sourceKPTranslateRepresentativeHaar K hζ T
local notation "μJ" => sourceKPTranslateCompactHaar K hζ T

theorem sourceKPTranslateRepresentativeToCompact_full_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving qJ νJ μJ := by
  letI : Countable Γ := sourceKPCuspRationalProjective_countable K
  unfold sourceKPTranslateCompactHaar
  exact quotient_quasiMeasurePreserving_of_domain
    (sourceKPTranslateRepresentativeDomain_isFundamental K hζ T 1
      (sourceKPFiniteTranslateLevel_le_conjugate_one K hζ T))
    qJ (sourceKPTranslateRepresentativeToCompact_measurable K hζ T)
    (sourceKPTranslateRepresentativeToCompact_rational K hζ T)

theorem sourceKPTranslateRepresentative_ae_forall_coset (p : XJ → Prop)
    (hp : ∀ᵐ x ∂νJ, p x) : ∀ᵐ x ∂ν, ∀ c : FJ, p (x.1,c) := by
  have h : ∀ᵐ a ∂μA, ∀ᵐ c ∂(Measure.count : Measure FJ), p (a,c) :=
    Measure.ae_ae_of_ae_prod hp
  have h' : ∀ᵐ a ∂μA, ∀ c : FJ, p (a,c) :=
    h.mono fun _ ha => Measure.ae_count_iff.mp ha
  exact Measure.quasiMeasurePreserving_fst.ae h'

end
end ArtinMatthews
