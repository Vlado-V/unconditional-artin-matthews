module

public import ArtinMatthews.IdealSlotPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The literal endpoint symmetrizations extend a bound on symmetric
vectors to the full original harmonic Hilbert space. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealOperatorWithLaws_input_average {I G : Type*} [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {k ell : ℕ} (freshLaw auxLaw : ∀ j,↥(P j) → ℝ)
    (patterns : Finset I) (C : I → G → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ ν,GiantTwoSidedPatternCoefficient P (C ν) ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ K (idealSlotAverage f)=
      idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ K f := by
  unfold idealOperatorWithLaws
  rw [idealSlotAverage_fixed _ (idealSlotAverage_symmetric f)]

theorem idealOperatorWithLaws_energy_from_symmetric {I G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (freshLaw auxLaw : ∀ j,↥(P j) → ℝ) (patterns : Finset I)
    (C : I → G → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ ν,GiantTwoSidedPatternCoefficient P (C ν) ell) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ f,IdealSymmetric f →
      idealLabelEnergy P (k+ell) (idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ K f) ≤
        B*idealLabelEnergy P (k+ell) f)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelEnergy P (k+ell) (idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ K f) ≤
      B*idealLabelEnergy P (k+ell) f := by
  rw [← idealOperatorWithLaws_input_average freshLaw auxLaw patterns C Θ ζ K f]
  exact (hbound (idealSlotAverage f) (idealSlotAverage_symmetric f)).trans
    (mul_le_mul_of_nonneg_left (idealSlotAverage_energy_le P hV f) hB)

end
end ArtinMatthews
