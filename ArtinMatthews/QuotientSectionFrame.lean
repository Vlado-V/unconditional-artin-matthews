module

public import Mathlib.Topology.Algebra.Group.Quotient


set_option backward.privateInPublic true
@[expose] public section

/-! A continuous section of G → G/K gives the actual group frame G ≃ Q × K. -/
namespace ArtinMatthews
open Topology
noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (K : Subgroup G) (sectionMap : G ⧸ K → G)
variable (sectionRightInverse : ∀ q : G ⧸ K, QuotientGroup.mk (sectionMap q) = q)

def quotientSectionFrame (g : G) : (G ⧸ K) × K :=
  (QuotientGroup.mk g, ⟨(sectionMap (QuotientGroup.mk g))⁻¹ * g,
    QuotientGroup.eq.mp (sectionRightInverse (QuotientGroup.mk g))⟩)

def quotientSectionFrameInverse (p : (G ⧸ K) × K) : G :=
  sectionMap p.1 * p.2.val

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem quotientSectionFrameInverse_frame (g : G) :
    quotientSectionFrameInverse K sectionMap
      (quotientSectionFrame K sectionMap sectionRightInverse g) = g := by
  exact mul_inv_cancel_left _ _

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem quotientSectionFrame_frameInverse (p : (G ⧸ K) × K) :
    quotientSectionFrame K sectionMap sectionRightInverse
      (quotientSectionFrameInverse K sectionMap p) = p := by
  have hq : QuotientGroup.mk (sectionMap p.1 * p.2.val) = p.1 := by
    rw [QuotientGroup.mk_mul_of_mem _ p.2.property, sectionRightInverse]
  apply Prod.ext
  · exact hq
  · apply Subtype.ext
    change (sectionMap (QuotientGroup.mk (sectionMap p.1 * p.2.val)))⁻¹ *
      (sectionMap p.1 * p.2.val) = p.2.val
    rw [hq, inv_mul_cancel_left]

theorem quotientSectionFrame_continuous (continuousSection : Continuous sectionMap) :
    Continuous (quotientSectionFrame K sectionMap sectionRightInverse) := by
  apply Continuous.prodMk QuotientGroup.continuous_mk
  exact (((continuousSection.comp QuotientGroup.continuous_mk).inv).mul
    continuous_id).subtype_mk _

theorem quotientSectionFrameInverse_continuous (continuousSection : Continuous sectionMap) :
    Continuous (quotientSectionFrameInverse K sectionMap) :=
  (continuousSection.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

def quotientSectionFrameHomeomorph (continuousSection : Continuous sectionMap) :
    G ≃ₜ ((G ⧸ K) × K) where
  toFun := quotientSectionFrame K sectionMap sectionRightInverse
  invFun := quotientSectionFrameInverse K sectionMap
  left_inv := quotientSectionFrameInverse_frame K sectionMap sectionRightInverse
  right_inv := quotientSectionFrame_frameInverse K sectionMap sectionRightInverse
  continuous_toFun := quotientSectionFrame_continuous K sectionMap sectionRightInverse continuousSection
  continuous_invFun := quotientSectionFrameInverse_continuous K sectionMap continuousSection

end
end ArtinMatthews
