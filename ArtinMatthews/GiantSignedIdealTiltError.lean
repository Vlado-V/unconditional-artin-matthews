module

public import ArtinMatthews.GiantSignedIdealOperatorBound
public import ArtinMatthews.GiantSignedTiltDifference


set_option backward.privateInPublic true
@[expose] public section

/-! The fresh-law change is bounded in the original harmonic energy by
its derived coefficient error. Both endpoint slot averages are retained. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedIdeal_tilt_error_energy
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (hP : ∀ j p, p ∈ P j → p.Prime)
    (r : ∀ j, P j → ℝ) (hr : ∀ j p, 1 ≤ r j p)
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (cost : I → ℝ) (hcost : ∀ v ∈ patterns, 0 ≤ cost v)
    (hK : ∀ v ∈ patterns, ∀ a b aux, ‖K v a b aux‖ ≤ cost v)
    (η : ℝ) (hη : 0 ≤ η)
    (hFresh : ∀ v ∈ patterns, ∀ b : MarkedPhysicalMarking P (k+ell),
      idealFreshTargetMass r (C v) b ≤ 1 + η)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelEnergy P (k+ell)
      (fun a => idealOperatorWithLaws
        (fun j p => markedHarmonicAtom (P j) p * r j p)
        (fun j => markedHarmonicAtom (P j)) patterns C Θ ζ K f a -
          idealOperator patterns C Θ ζ K f a) ≤
      (η * ∑ v ∈ patterns, cost v) ^ 2 * idealLabelEnergy P (k+ell) f := by
  classical
  let D : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell := fun v a b aux =>
    K v a b aux * ((idealFreshTargetMass r (C v) b - 1 : ℝ) : ℂ)
  have hD (v : I) (hv : v ∈ patterns) (a b : MarkedPhysicalMarking P (k+ell))
      (aux : GiantTwoSidedPatternAuxiliary P (C v)) : ‖D v a b aux‖ ≤ η * cost v := by
    have he := idealTiltCoefficient_difference_norm r hr (C v) (K v) (1 + η) (hFresh v hv) a b aux
    rw [idealTiltCoefficient_difference] at he
    change ‖D v a b aux‖ ≤ _ at he
    have hc := mul_le_mul_of_nonneg_right (hK v hv a b aux) hη
    nlinarith
  have heq : (fun a => idealOperatorWithLaws
        (fun j p => markedHarmonicAtom (P j) p * r j p)
        (fun j => markedHarmonicAtom (P j)) patterns C Θ ζ K f a -
          idealOperator patterns C Θ ζ K f a) = idealOperator patterns C Θ ζ D f := by
    funext a
    exact giantSignedIdeal_tilt_difference (fun j => markedHarmonicAtom (P j)) r patterns C Θ ζ K f a
  rw [heq]
  have he := giantSignedIdealOperator_absolute_energy hV hP patterns C Θ ζ D
    (fun v => η * cost v) (fun v hv => mul_nonneg hη (hcost v hv)) hD f
  simpa only [Finset.mul_sum] using he

end
end ArtinMatthews
