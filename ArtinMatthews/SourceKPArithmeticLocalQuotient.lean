module

public import ArtinMatthews.SourceKPArithmeticDiscreteness
public import ArtinMatthews.SourceKPFiniteOrbit
public import Mathlib.Topology.Covering.Quotient
public import ArtinMatthews.CompactHomogeneousQuotient


set_option backward.privateInPublic true
@[expose] public section

/-! Local quotient maps and finite isotropy for the actual arithmetic
component groups. -/
namespace ArtinMatthews
open NumberField Matrix Topology Filter
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPArchComponentSubgroup_properlyDiscontinuous
    (b : SourceKPFiniteLevelFiber K hζ) :
    ProperlyDiscontinuousSMul (sourceKPArchComponentSubgroup K hζ b)
      (PGL(2, InfiniteAdeleRing K)) := by
  apply Subgroup.properlyDiscontinuousSMul_of_tendsto_cofinite
  rw [tendsto_cofinite_cocompact_iff]
  intro C hC
  exact sourceKPArchComponentSubgroup_compact_finite K hζ b C hC

theorem sourceKPArchComponent_localHomeomorph (b : SourceKPFiniteLevelFiber K hζ) :
    IsLocalHomeomorph (Quotient.mk
      (QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ b))) := by
  apply Topology.IsQuotientMap.isLocalHomeomorph_of_properlyDiscontinuousSMul
    (G := sourceKPArchComponentSubgroup K hζ b) isQuotientMap_quotient_mk'
  exact Quotient.eq''

theorem sourceKPArchComponent_localChart (b : SourceKPFiniteLevelFiber K hζ)
    (g : PGL(2, InfiniteAdeleRing K)) :
    ∃ e : OpenPartialHomeomorph (PGL(2, InfiniteAdeleRing K))
      (Quotient (QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ b))),
      g ∈ e.source ∧ (Quotient.mk _ : PGL(2, InfiniteAdeleRing K) → _) = e :=
  sourceKPArchComponent_localHomeomorph K hζ b g


theorem sourceKPArchComponentPoint_isOpenMap (b : SourceKPFiniteLevelFiber K hζ) :
    IsOpenMap (sourceKPArchComponentPoint K hζ b) := by
  let : ContinuousConstSMul (PGL(2, K)) (SourceKPFiniteLevelSpace K hζ) :=
    ⟨sourceKPFiniteLevel_rational_continuous K hζ⟩
  have hq : IsOpenMap (Quotient.mk
      (MulAction.orbitRel (PGL(2, K)) (SourceKPFiniteLevelSpace K hζ))) :=
    isOpenMap_quotient_mk'_mul
  intro U hU
  have he : sourceKPArchComponentPoint K hζ b '' U =
      Quotient.mk (MulAction.orbitRel (PGL(2, K)) (SourceKPFiniteLevelSpace K hζ)) ''
        (U ×ˢ {b}) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(a,b), ⟨ha, rfl⟩, rfl⟩
    · rintro ⟨⟨a,c⟩, ⟨ha,hc⟩, rfl⟩
      have hc' : c = b := hc
      subst c
      exact ⟨a,ha,rfl⟩
  rw [he]
  exact hq _ (hU.prod (isOpen_discrete _))

theorem sourceKPArchComponentEmbedding_isOpenMap (b : SourceKPFiniteLevelFiber K hζ) :
    IsOpenMap (sourceKPArchComponentEmbedding K hζ b) := by
  intro U hU
  have he : sourceKPArchComponentEmbedding K hζ b '' U =
      sourceKPArchComponentPoint K hζ b ''
        ((Quotient.mk (QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ b))) ⁻¹' U) := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      obtain ⟨g,rfl⟩ := Quotient.mk_surjective a
      exact ⟨g,ha,rfl⟩
    · rintro ⟨g,hg,rfl⟩
      exact ⟨Quotient.mk _ g,hg,rfl⟩
  rw [he]
  exact sourceKPArchComponentPoint_isOpenMap K hζ b _ (hU.preimage continuous_quot_mk)

theorem sourceKPArchComponentEmbedding_isOpenEmbedding (b : SourceKPFiniteLevelFiber K hζ) :
    IsOpenEmbedding (sourceKPArchComponentEmbedding K hζ b) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (sourceKPArchComponentEmbedding_continuous K hζ b)
    (sourceKPArchComponentEmbedding K hζ b).injective
    (sourceKPArchComponentEmbedding_isOpenMap K hζ b)

theorem sourceKPArchComponentPoint_localHomeomorph (b : SourceKPFiniteLevelFiber K hζ) :
    IsLocalHomeomorph (sourceKPArchComponentPoint K hζ b) :=
  (sourceKPArchComponentEmbedding_isOpenEmbedding K hζ b).isLocalHomeomorph.comp
    (sourceKPArchComponent_localHomeomorph K hζ b)

theorem sourceKPArchComponentPoint_localChart (b : SourceKPFiniteLevelFiber K hζ)
    (g : PGL(2, InfiniteAdeleRing K)) :
    ∃ e : OpenPartialHomeomorph (PGL(2, InfiniteAdeleRing K)) (SourceKPAutomorphicLevel K hζ),
      g ∈ e.source ∧ sourceKPArchComponentPoint K hζ b = e :=
  sourceKPArchComponentPoint_localHomeomorph K hζ b g

theorem sourceKPArchComponent_disjoint_neighborhood (b : SourceKPFiniteLevelFiber K hζ)
    (g : PGL(2, InfiniteAdeleRing K)) :
    ∃ U ∈ 𝓝 g, ∀ γ : sourceKPArchComponentSubgroup K hζ b,
      γ ≠ 1 → Disjoint ((fun a => γ.val * a) '' U) U := by
  obtain ⟨U, hU, hdisj⟩ := ProperlyDiscontinuousSMul.exists_nhds_disjoint_image
    (sourceKPArchComponentSubgroup K hζ b) g
  refine ⟨U, hU, fun γ hγ => hdisj γ ?_⟩
  intro he
  apply hγ
  apply Subtype.ext
  change γ.val * g = g at he
  exact mul_right_cancel (he.trans (one_mul g).symm)




theorem sourceKPArchHomogeneous_finite_stabilizer
    (b : SourceKPFiniteLevelFiber K hζ)
    (L : Subgroup (PGL(2, InfiniteAdeleRing K)))
    (hL : IsCompact (L : Set (PGL(2, InfiniteAdeleRing K))))
    (x : PGL(2, InfiniteAdeleRing K) ⧸ L) :
    (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) x :
      Set (sourceKPArchComponentSubgroup K hζ b)).Finite := by
  let := sourceCompactSubgroup_quotient_properlyDiscontinuous
    (sourceKPArchComponentSubgroup K hζ b) L hL
  exact ProperlyDiscontinuousSMul.finite_stabilizer x

theorem sourceKPArchHomogeneous_disjoint_neighborhood
    (b : SourceKPFiniteLevelFiber K hζ)
    (L : Subgroup (PGL(2, InfiniteAdeleRing K)))
    (hL : IsCompact (L : Set (PGL(2, InfiniteAdeleRing K))))
    (x : PGL(2, InfiniteAdeleRing K) ⧸ L) :
    ∃ U ∈ 𝓝 x, ∀ γ : sourceKPArchComponentSubgroup K hζ b,
      γ • x ≠ x → Disjoint ((γ • ·) '' U) U := by
  let : IsClosed (L : Set (PGL(2, InfiniteAdeleRing K))) := hL.isClosed
  let := sourceCompactSubgroup_quotient_properlyDiscontinuous
    (sourceKPArchComponentSubgroup K hζ b) L hL
  exact ProperlyDiscontinuousSMul.exists_nhds_disjoint_image
    (sourceKPArchComponentSubgroup K hζ b) x

end
end ArtinMatthews
