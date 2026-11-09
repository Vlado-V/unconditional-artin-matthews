module

public import ArtinMatthews.QuotientSectionFrame
public import Mathlib.Tactic.Group


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Topology
noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (K : Subgroup G) (sectionMap : G ⧸ K → G)
variable (sectionRightInverse : ∀ q : G ⧸ K, QuotientGroup.mk (sectionMap q) = q)

def quotientSectionCocycle (g : G) (q : G ⧸ K) : K :=
  ⟨(sectionMap (g • q))⁻¹ * (g * sectionMap q), by
    apply QuotientGroup.eq.mp
    rw [sectionRightInverse]
    change g • q = g • QuotientGroup.mk (sectionMap q)
    rw [sectionRightInverse]⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem quotientSectionFrame_mul (g h : G) :
    quotientSectionFrame K sectionMap sectionRightInverse (g*h) =
      (g • (quotientSectionFrame K sectionMap sectionRightInverse h).1,
       quotientSectionCocycle K sectionMap sectionRightInverse g
         (quotientSectionFrame K sectionMap sectionRightInverse h).1 *
         (quotientSectionFrame K sectionMap sectionRightInverse h).2) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (sectionMap (QuotientGroup.mk (g*h)))⁻¹ * (g*h) =
      ((sectionMap (g • QuotientGroup.mk h))⁻¹ * (g * sectionMap (QuotientGroup.mk h))) *
        ((sectionMap (QuotientGroup.mk h))⁻¹ * h)
    change (sectionMap (g • QuotientGroup.mk h))⁻¹ * (g*h) = _
    group

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem quotientSectionCocycle_one (q : G ⧸ K) :
    quotientSectionCocycle K sectionMap sectionRightInverse 1 q = 1 := by
  apply Subtype.ext
  change (sectionMap (1 • q))⁻¹ * (1 * sectionMap q) = 1
  rw [one_smul,one_mul,inv_mul_cancel]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem quotientSectionCocycle_mul (g h : G) (q : G ⧸ K) :
    quotientSectionCocycle K sectionMap sectionRightInverse (g*h) q =
      quotientSectionCocycle K sectionMap sectionRightInverse g (h • q) *
        quotientSectionCocycle K sectionMap sectionRightInverse h q := by
  apply Subtype.ext
  change (sectionMap ((g*h) • q))⁻¹ * ((g*h) * sectionMap q) =
    ((sectionMap (g • h • q))⁻¹ * (g * sectionMap (h • q))) *
      ((sectionMap (h • q))⁻¹ * (h * sectionMap q))
  rw [mul_smul]
  group

theorem quotientSectionCocycle_continuous (continuousSection : Continuous sectionMap) (g : G) :
    Continuous (quotientSectionCocycle K sectionMap sectionRightInverse g) := by
  apply Continuous.subtype_mk
  exact ((continuousSection.comp (continuous_const_smul g)).inv).mul
    (continuous_const.mul continuousSection)

end
end ArtinMatthews
