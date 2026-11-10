module

public import Mathlib.Topology.Algebra.Group.Quotient


set_option backward.privateInPublic true
@[expose] public section

/-! Proper discontinuity on a compact-subgroup homogeneous quotient. -/
namespace ArtinMatthews
open Topology Filter
noncomputable section

section CompactHomogeneousSpace
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem sourceCompactSubgroup_quotient_proper (L : Subgroup G)
    (hL : IsCompact (L : Set G)) : IsProperMap (QuotientGroup.mk (s := L)) := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨QuotientGroup.continuous_mk, QuotientGroup.isClosedMap_coe hL, ?_⟩
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have he : (QuotientGroup.mk (s := L)) ⁻¹' {QuotientGroup.mk g} =
      (fun l : G => g * l) '' (L : Set G) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · intro h
      have hm : g⁻¹ * a ∈ L := QuotientGroup.eq.mp h.symm
      exact ⟨g⁻¹ * a, hm, by simp⟩
    · rintro ⟨l, hl, rfl⟩
      apply QuotientGroup.eq.mpr
      simpa using L.inv_mem hl
  rw [he]
  exact hL.image (continuous_const.mul continuous_id)


theorem sourceCompactSubgroup_quotient_properlyDiscontinuous
    (Γ L : Subgroup G) [ProperlyDiscontinuousSMul Γ G]
    (hL : IsCompact (L : Set G)) : ProperlyDiscontinuousSMul Γ (G ⧸ L) := by
  refine ⟨?_⟩
  intro U V hU hV
  have hq := sourceCompactSubgroup_quotient_proper L hL
  have hf := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
    (Γ := Γ) (hq.isCompact_preimage hU) (hq.isCompact_preimage hV)
  apply hf.subset
  rintro γ ⟨x, ⟨u, hu, rfl⟩, hx⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
  exact ⟨γ • g, ⟨g, hu, rfl⟩, hx⟩

end CompactHomogeneousSpace

end
end ArtinMatthews
