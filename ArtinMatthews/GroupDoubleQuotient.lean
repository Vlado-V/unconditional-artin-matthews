module

public import ArtinMatthews.CommutingOrbitQuotient
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Topology.Algebra.Group.Quotient


set_option backward.privateInPublic true
@[expose] public section

/-! The two iterated orbit quotients of a topological group by left and
right subgroups are the literal double quotient. -/
namespace ArtinMatthews
open Topology MulOpposite
noncomputable section

variable {G : Type*} [Group G]

instance sourceLeftQuotient_rightAction (H : Subgroup G) :
    MulAction Gᵐᵒᵖ (Quotient (QuotientGroup.rightRel H)) :=
  sourceCommutingOrbitAction H Gᵐᵒᵖ G

@[simp] theorem sourceLeftQuotient_rightAction_mk (H : Subgroup G) (k : Gᵐᵒᵖ) (g : G) :
    k • (Quotient.mk (QuotientGroup.rightRel H) g) =
      Quotient.mk (QuotientGroup.rightRel H) (g * unop k) := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

instance sourceLeftQuotient_rightContinuous (H : Subgroup G) :
    ContinuousSMul Gᵐᵒᵖ (Quotient (QuotientGroup.rightRel H)) :=
  sourceCommutingOrbitAction_continuous H Gᵐᵒᵖ G

abbrev SourceLeftThenRightQuotient (H L : Subgroup G) :=
  Quotient (MulAction.orbitRel L.op (Quotient (QuotientGroup.rightRel H)))

abbrev SourceRightThenLeftQuotient (H L : Subgroup G) :=
  Quotient (MulAction.orbitRel H (G ⧸ L))

def sourceLeftThenRightMk (H L : Subgroup G) (g : G) : SourceLeftThenRightQuotient H L :=
  Quotient.mk _ (Quotient.mk _ g)

def sourceRightThenLeftMk (H L : Subgroup G) (g : G) : SourceRightThenLeftQuotient H L :=
  Quotient.mk _ (QuotientGroup.mk g)

theorem sourceLeftThenRightMk_isOpenQuotientMap (H L : Subgroup G) :
    IsOpenQuotientMap (sourceLeftThenRightMk H L) := by
  have hleft : IsOpenQuotientMap (Quotient.mk (QuotientGroup.rightRel H)) :=
    MulAction.isOpenQuotientMap_quotientMk
  have hright : IsOpenQuotientMap
      (Quotient.mk (MulAction.orbitRel L.op (Quotient (QuotientGroup.rightRel H)))) :=
    MulAction.isOpenQuotientMap_quotientMk
  exact hright.comp hleft

theorem sourceRightThenLeftMk_isOpenQuotientMap (H L : Subgroup G) :
    IsOpenQuotientMap (sourceRightThenLeftMk H L) := by
  have hright : IsOpenQuotientMap (QuotientGroup.mk (s := L)) :=
    QuotientGroup.isOpenQuotientMap_mk
  have hleft : IsOpenQuotientMap (Quotient.mk (MulAction.orbitRel H (G ⧸ L))) :=
    MulAction.isOpenQuotientMap_quotientMk
  exact hleft.comp hright

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem sourceLeftThenRightMk_eq_iff (H L : Subgroup G) (a b : G) :
    sourceLeftThenRightMk H L a = sourceLeftThenRightMk H L b ↔
      DoubleCoset.setoid (H : Set G) (L : Set G) a b := by
  rw [DoubleCoset.rel_iff]
  constructor
  · intro hab
    obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hab.symm)
    obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hk.symm)
    refine ⟨h.val,h.property,unop k.val,k.property,?_⟩
    have hh' : h.val * (a * unop k.val) = b := hh
    simpa only [← mul_assoc] using hh'.symm
  · rintro ⟨h,hh,k,hk,rfl⟩
    apply Eq.symm
    apply Quotient.sound
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨op k,hk⟩,?_⟩
    apply Quotient.sound
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨h⁻¹,H.inv_mem hh⟩,?_⟩
    change h⁻¹ * (h * a * k) = a * k
    simp [mul_assoc]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem sourceRightThenLeftMk_eq_iff (H L : Subgroup G) (a b : G) :
    sourceRightThenLeftMk H L a = sourceRightThenLeftMk H L b ↔
      DoubleCoset.setoid (H : Set G) (L : Set G) a b := by
  rw [DoubleCoset.rel_iff]
  constructor
  · intro hab
    obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hab.symm)
    have hk : (h.val * a)⁻¹ * b ∈ L := QuotientGroup.eq.mp hh
    exact ⟨h.val,h.property,(h.val * a)⁻¹ * b,hk,
      (mul_inv_cancel_left (h.val * a) b).symm⟩
  · rintro ⟨h,hh,k,hk,rfl⟩
    apply Eq.symm
    apply Quotient.sound
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨h,hh⟩,?_⟩
    apply QuotientGroup.eq.mpr
    change (h * a)⁻¹ * (h * a * k) ∈ L
    simpa only [inv_mul_cancel_left] using hk

def sourceDoubleLeftThenRightHomeomorph (H L : Subgroup G) :
    Quotient (DoubleCoset.setoid (H : Set G) (L : Set G)) ≃ₜ SourceLeftThenRightQuotient H L :=
  sourceQuotientHomeomorph _
    ⟨sourceLeftThenRightMk H L,(sourceLeftThenRightMk_isOpenQuotientMap H L).continuous⟩
    (sourceLeftThenRightMk_isOpenQuotientMap H L).isQuotientMap
    (fun a b => (sourceLeftThenRightMk_eq_iff H L a b).symm)

def sourceDoubleRightThenLeftHomeomorph (H L : Subgroup G) :
    Quotient (DoubleCoset.setoid (H : Set G) (L : Set G)) ≃ₜ SourceRightThenLeftQuotient H L :=
  sourceQuotientHomeomorph _
    ⟨sourceRightThenLeftMk H L,(sourceRightThenLeftMk_isOpenQuotientMap H L).continuous⟩
    (sourceRightThenLeftMk_isOpenQuotientMap H L).isQuotientMap
    (fun a b => (sourceRightThenLeftMk_eq_iff H L a b).symm)

@[simp] theorem sourceDoubleLeftThenRightHomeomorph_mk (H L : Subgroup G) (g : G) :
    sourceDoubleLeftThenRightHomeomorph H L (Quotient.mk _ g) = sourceLeftThenRightMk H L g := rfl

@[simp] theorem sourceDoubleRightThenLeftHomeomorph_mk (H L : Subgroup G) (g : G) :
    sourceDoubleRightThenLeftHomeomorph H L (Quotient.mk _ g) = sourceRightThenLeftMk H L g := rfl

end
end ArtinMatthews
