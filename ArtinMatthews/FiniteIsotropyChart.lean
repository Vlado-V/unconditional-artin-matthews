module

public import ArtinMatthews.CommutingOrbitQuotient
public import Mathlib.Tactic.Bound.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Precompact finite-isotropy quotient charts for a properly discontinuous action. -/
namespace ArtinMatthews
open Topology Filter
noncomputable section

structure SourceFiniteIsotropyChart (Γ X : Type*) [Group Γ] [TopologicalSpace X]
    [MulAction Γ X] (p : X) where
  domain : SubMulAction (MulAction.stabilizer Γ p) X
  isOpen_domain : IsOpen (domain : Set X)
  center_mem : p ∈ domain
  isCompact_closure : IsCompact (closure (domain : Set X))
  finite_stabilizer : (MulAction.stabilizer Γ p : Set Γ).Finite
  separated : ∀ γ : Γ, γ • p ≠ p →
    Disjoint ((γ • ·) '' (domain : Set X)) (domain : Set X)

variable {Γ X : Type*} [Group Γ] [TopologicalSpace X] [MulAction Γ X] {p : X}

def sourceFiniteChartProjection (c : SourceFiniteIsotropyChart Γ X p) (x : c.domain) :
    Quotient (MulAction.orbitRel Γ X) := Quotient.mk _ x.val

def sourceFiniteChartRangeMap (c : SourceFiniteIsotropyChart Γ X p) :
    c.domain → Set.range (sourceFiniteChartProjection c) :=
  Set.rangeFactorization (sourceFiniteChartProjection c)

theorem sourceFiniteChartRangeMap_eq_iff (c : SourceFiniteIsotropyChart Γ X p)
    (x y : c.domain) :
    sourceFiniteChartRangeMap c x = sourceFiniteChartRangeMap c y ↔
      MulAction.orbitRel (MulAction.stabilizer Γ p) c.domain x y := by
  constructor
  · intro hxy
    have h := congrArg Subtype.val hxy
    obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h)
    have hfix : γ • p = p := by
      by_contra hnot
      exact Set.disjoint_left.mp (c.separated γ hnot) ⟨y.val,y.property,hγ⟩ x.property
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨⟨γ,hfix⟩,Subtype.ext hγ⟩
  · intro hxy
    obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp hxy
    apply Subtype.ext
    apply Quotient.sound
    exact MulAction.mem_orbit_iff.mpr ⟨γ.val,congrArg Subtype.val hγ⟩

variable [ContinuousConstSMul Γ X]

omit [ContinuousConstSMul Γ X] in
theorem sourceFiniteChartProjection_continuous (c : SourceFiniteIsotropyChart Γ X p) :
    Continuous (sourceFiniteChartProjection c) :=
  continuous_quot_mk.comp continuous_subtype_val

theorem sourceFiniteChartProjection_isOpenMap (c : SourceFiniteIsotropyChart Γ X p) :
    IsOpenMap (sourceFiniteChartProjection c) :=
  isOpenMap_quotient_mk'_mul.comp c.isOpen_domain.isOpenEmbedding_subtypeVal.isOpenMap

theorem sourceFiniteChartRangeMap_isOpenQuotientMap (c : SourceFiniteIsotropyChart Γ X p) :
    IsOpenQuotientMap (sourceFiniteChartRangeMap c) := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨y,⟨x,rfl⟩⟩
    exact ⟨x,rfl⟩
  · exact (sourceFiniteChartProjection_continuous c).subtype_mk _
  · exact (sourceFiniteChartProjection_isOpenMap c).subtype_mk _

def sourceFiniteChartQuotientHomeomorph (c : SourceFiniteIsotropyChart Γ X p) :
    Quotient (MulAction.orbitRel (MulAction.stabilizer Γ p) c.domain) ≃ₜ
      Set.range (sourceFiniteChartProjection c) :=
  sourceQuotientHomeomorph _
    ⟨sourceFiniteChartRangeMap c,(sourceFiniteChartRangeMap_isOpenQuotientMap c).continuous⟩
    (sourceFiniteChartRangeMap_isOpenQuotientMap c).isQuotientMap
    (fun x y => (sourceFiniteChartRangeMap_eq_iff c x y).symm)

@[simp] theorem sourceFiniteChartQuotientHomeomorph_mk
    (c : SourceFiniteIsotropyChart Γ X p) (x : c.domain) :
    (sourceFiniteChartQuotientHomeomorph c (Quotient.mk _ x) : Quotient (MulAction.orbitRel Γ X)) =
      Quotient.mk _ x.val := rfl

theorem sourceFiniteChartProjection_range_open (c : SourceFiniteIsotropyChart Γ X p) :
    IsOpen (Set.range (sourceFiniteChartProjection c)) :=
  (sourceFiniteChartProjection_isOpenMap c).isOpen_range

variable (Γ X) [ProperlyDiscontinuousSMul Γ X] [T2Space X] [LocallyCompactSpace X]

theorem sourceFiniteIsotropyChart_exists (p : X) : Nonempty (SourceFiniteIsotropyChart Γ X p) := by
  classical
  obtain ⟨V,hV,hsep⟩ := ProperlyDiscontinuousSMul.exists_nhds_disjoint_image Γ p
  obtain ⟨C,hC,hCp⟩ := exists_compact_mem_nhds p
  obtain ⟨W,hWsub,hWo,hpW⟩ := mem_nhds_iff.mp (inter_mem hV hCp)
  have hfin := ProperlyDiscontinuousSMul.finite_stabilizer (Γ := Γ) p
  let H := MulAction.stabilizer Γ p
  let : Fintype H := hfin.fintype
  let U : SubMulAction H X := {
    carrier := {x | ∀ h : H, (h : Γ) • x ∈ W}
    smul_mem' := by
      intro h x hx k
      change (k : Γ) • ((h : Γ) • x) ∈ W
      simpa only [Subgroup.coe_mul, mul_smul] using hx (k*h) }
  have hUW : (U : Set X) ⊆ W := by
    intro x hx
    simpa only [Subgroup.coe_one, one_smul] using hx 1
  refine ⟨{
    domain := U
    isOpen_domain := ?_
    center_mem := ?_
    isCompact_closure := ?_
    finite_stabilizer := hfin
    separated := ?_ }⟩
  · change IsOpen {x | ∀ h : H, (h : Γ) • x ∈ W}
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun h => hWo.preimage (continuous_const_smul (h : Γ))
  · intro h
    rw [h.property]
    exact hpW
  · exact hC.of_isClosed_subset isClosed_closure
      (closure_minimal (hUW.trans fun x hx => (hWsub hx).2) hC.isClosed)
  · intro γ hγ
    have hUV : (U : Set X) ⊆ V := hUW.trans fun x hx => (hWsub hx).1
    exact (hsep γ hγ).mono (Set.image_mono hUV) hUV

def sourceFiniteIsotropyChartAt (p : X) : SourceFiniteIsotropyChart Γ X p :=
  Classical.choice (sourceFiniteIsotropyChart_exists Γ X p)

end
end ArtinMatthews
