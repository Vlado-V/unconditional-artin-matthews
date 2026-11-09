module

public import ArtinMatthews.GiantSignedIdealTransition
public import ArtinMatthews.GiantSignedIdealAuxiliary


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute energy of the actual ideal row, with its original auxiliary law. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantSignedIdealPattern_average_auxiliary
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (C : J → Finset (Fin k)) (Θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient P C ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
        (fun j => markedHarmonicAtom (P j)) C Θ ζ K f a =
      ∑ b : MarkedPhysicalMarking P (k+ell),
        (giantSignedIdealTransition C a b : ℂ) *
          giantSignedIdealAveragedMultiplier C Θ ζ K a b * f b := by
  classical
  unfold idealPatternApplyWithLaws giantSignedIdealAveragedMultiplier
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro aux _
  by_cases h : IdealCopied C a b
  · simp only [giantSignedIdealTransition, h, ite_true]
    ring
  · simp [giantSignedIdealTransition, h]

theorem giantSignedIdealPattern_energy
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (hP : ∀ j p, p ∈ P j → p.Prime)
    (C : J → Finset (Fin k)) (Θ ζ R : ℝ) (K : GiantTwoSidedPatternCoefficient P C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ R) (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelEnergy P (k+ell)
        (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
          (fun j => markedHarmonicAtom (P j)) C Θ ζ K f) ≤
      R ^ 2 * idealLabelEnergy P (k+ell) f := by
  unfold idealLabelEnergy
  simp_rw [giantSignedIdealPattern_average_auxiliary]
  exact giantSignedIdealTransition_energy hV C
    (giantSignedIdealAveragedMultiplier C Θ ζ K) R
    (giantSignedIdealAveragedMultiplier_norm hV hP C Θ ζ R K hK) f

end
end ArtinMatthews
