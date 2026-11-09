module

public import ArtinMatthews.MarkedPhysicalPadCollisionMass
public import ArtinMatthews.MarkedMajorLabelSplit


set_option backward.privateInPublic true
@[expose] public section

/-! The exact harmonic weight of each fixed pair of unshared labels.
The probability is formed after fixing both labels, so no adaptive
choice of labels enters the collision estimate. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalMass_two_labelMass_sq {J : Type*} [Fintype J] (P : J → Finset ℕ) :
    markedPhysicalMass (fun j => bandReciprocalMass (P j)) 2 = (markedMajorLabelMass P)^2 := by
  rw [markedPhysicalMass,markedMajorLabelMass,Finset.prod_pow]

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (pads : ℕ) (hV : ∀ j,0 < bandReciprocalMass (P j))
  (b a : (j : J) → ↥(P j))

include hV

theorem markedPhysicalPadHarmonicMass_survival :
    (∑ c : MarkedPhysicalMarking P pads,
      if ¬MarkedPhysicalPadCollisionEvent P pads b a c then
        markedPhysicalPadHarmonicMass P pads c else 0)=
      1-markedPhysicalPadCollisionMass P pads b a := by
  let μ := markedPhysicalPadHarmonicMass P pads
  let E := MarkedPhysicalPadCollisionEvent P pads b a
  have h (c : MarkedPhysicalMarking P pads) :
      (if ¬E c then μ c else 0) = μ c-(if E c then 1 else 0)*μ c := by
    by_cases hc : E c <;> simp [hc]
  change (∑ c,if ¬E c then μ c else 0)=_
  simp_rw [h]
  rw [Finset.sum_sub_distrib]
  change (∑ c,markedPhysicalPadHarmonicMass P pads c)-markedPhysicalPadCollisionMass P pads b a=_
  rw [markedPhysicalPadHarmonicMass_sum P pads hV]

theorem markedPhysicalPadHarmonicMass_survival_weighted (z : ℂ) :
    (∑ c : MarkedPhysicalMarking P pads,(markedPhysicalPadHarmonicMass P pads c:ℂ)*
      (if ¬MarkedPhysicalPadCollisionEvent P pads b a c then z else 0))=
      ((1-markedPhysicalPadCollisionMass P pads b a:ℝ):ℂ)*z := by
  rw [← markedPhysicalPadHarmonicMass_survival P pads hV b a,Complex.ofReal_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : MarkedPhysicalPadCollisionEvent P pads b a c <;> simp [hc]

end
end ArtinMatthews
