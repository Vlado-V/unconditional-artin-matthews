module

public import ArtinMatthews.GiantSignedIdealPatternBound
public import ArtinMatthews.GiantSignedIdealEnergySum
public import ArtinMatthews.IdealSlotSymmetry


set_option backward.privateInPublic true
@[expose] public section

/-! The actual two-sided slot average has the full coefficient-budget bound. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedIdealOperator_absolute_energy
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (hP : ∀ j p, p ∈ P j → p.Prime)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (cost : I → ℝ) (hcost : ∀ v ∈ patterns, 0 ≤ cost v)
    (hK : ∀ v ∈ patterns, ∀ a b aux, ‖K v a b aux‖ ≤ cost v)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelEnergy P (k+ell) (idealOperator patterns C Θ ζ K f) ≤
      (∑ v ∈ patterns, cost v) ^ 2 * idealLabelEnergy P (k+ell) f := by
  classical
  let μ : ∀ j, P j → ℝ := fun j => markedHarmonicAtom (P j)
  let T (v : I) := idealPatternApplyWithLaws μ μ (C v) Θ ζ (K v) (idealSlotAverage f)
  have heach (v : I) (hv : v ∈ patterns) :
      idealLabelEnergy P (k+ell) (T v) ≤ (cost v) ^ 2 *
        idealLabelEnergy P (k+ell) (idealSlotAverage f) :=
    giantSignedIdealPattern_energy hV hP (C v) Θ ζ (cost v) (K v) (hK v hv) _
  have hsum := giantSignedIdealEnergy_sum hV patterns cost hcost (idealSlotAverage f) T heach
  unfold idealOperator idealOperatorWithLaws
  calc
    _ ≤ idealLabelEnergy P (k+ell) (fun a => ∑ v ∈ patterns, T v a) :=
      idealSlotAverage_energy_le P hV _
    _ ≤ (∑ v ∈ patterns, cost v) ^ 2 * idealLabelEnergy P (k+ell) (idealSlotAverage f) := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left (idealSlotAverage_energy_le P hV f) (sq_nonneg _)

end
end ArtinMatthews
