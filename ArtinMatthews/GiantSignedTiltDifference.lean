module

public import ArtinMatthews.GiantSignedTiltOperator
public import ArtinMatthews.GiantSignedIdealLinearity


set_option backward.privateInPublic true
@[expose] public section

/-! The fresh-law perturbation is the literal coefficient difference. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedIdeal_tilt_difference
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (μ r : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealOperatorWithLaws (k := k) (ell := ell) (fun j p => μ j p * r j p) μ
        patterns C Θ ζ K f a - idealOperatorWithLaws μ μ patterns C Θ ζ K f a =
      idealOperatorWithLaws (k := k) (ell := ell) μ μ patterns C Θ ζ
        (fun v (a b : MarkedPhysicalMarking P (k+ell)) aux =>
          K v a b aux * ((idealFreshTargetMass (ell := ell) r (C v) b - 1 : ℝ) : ℂ)) f a := by
  classical
  let L : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell :=
    fun v a b aux => K v a b aux * (idealFreshTargetMass r (C v) b : ℂ)
  have he := congrArg (fun g => g a) (idealOperatorWithLaws_tilt μ r patterns C Θ ζ K f)
  change idealOperatorWithLaws (fun j p => μ j p * r j p) μ patterns C Θ ζ K f a =
    idealOperatorWithLaws μ μ patterns C Θ ζ L f a at he
  rw [he, ← giantSignedIdealOperator_sub μ μ patterns C Θ ζ L K f a]
  have hcoeff : (fun v a b aux => L v a b aux - K v a b aux) =
      (fun v a b aux => K v a b aux * ((idealFreshTargetMass r (C v) b - 1 : ℝ) : ℂ)) := by
    funext v a b aux
    exact idealTiltCoefficient_difference r (C v) (K v) a b aux
  rw [hcoeff]

theorem giantSignedTilt_originalEnergy_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} (μ r : ∀ j, P j → ℝ)
    (hμ : ∀ j p, 0 ≤ μ j p) (hr : ∀ j p, 1 ≤ r j p)
    (f : MarkedPhysicalMarking P M → ℂ) :
    (∑ a, giantSignedActiveMass μ a * ‖f a‖ ^ 2) ≤
      ∑ a, giantSignedActiveMass (fun j p => μ j p * r j p) a * ‖f a‖ ^ 2 := by
  classical
  apply Finset.sum_le_sum
  intro a _
  rw [giantSignedActiveMass_mul]
  have hm : 0 ≤ giantSignedActiveMass μ a :=
    Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun i _ => hμ j (a j i)
  have h := mul_le_mul_of_nonneg_left (giantSignedActiveMass_one_le r hr a)
    (mul_nonneg hm (sq_nonneg ‖f a‖))
  nlinarith

end
end ArtinMatthews
