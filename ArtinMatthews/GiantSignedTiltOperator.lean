module

public import ArtinMatthews.GiantSignedTiltDensity


set_option backward.privateInPublic true
@[expose] public section

/-! Changing the fresh law is exactly a multiplier in the literal ideal
coefficient. The auxiliary law remains the original law. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem idealPatternApplyWithLaws_tilt
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (μ r : ∀ j, P j → ℝ) (C : J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealPatternApplyWithLaws (fun j p => μ j p * r j p) μ C Θ ζ K f a =
      idealPatternApplyWithLaws μ μ C Θ ζ
        (fun a b aux => K a b aux * (idealFreshTargetMass r C b : ℂ)) f a := by
  classical
  unfold idealPatternApplyWithLaws
  apply Finset.sum_congr rfl
  intro aux _
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · rw [idealFreshTargetMass_mul, Complex.ofReal_mul]
    ring
  · rfl

theorem idealOperatorWithLaws_tilt
    {I J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (μ r : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealOperatorWithLaws (k := k) (ell := ell) (fun j p => μ j p * r j p) μ patterns C Θ ζ K f =
      idealOperatorWithLaws (k := k) (ell := ell) μ μ patterns C Θ ζ
        (fun v (a b : MarkedPhysicalMarking P (k+ell)) aux =>
          K v a b aux * (idealFreshTargetMass (ell := ell) r (C v) b : ℂ)) f := by
  classical
  funext a
  unfold idealOperatorWithLaws
  apply congrArg (fun F : MarkedPhysicalMarking P (k+ell) → ℂ => idealSlotAverage F a)
  funext b
  apply Finset.sum_congr rfl
  intro v _
  exact idealPatternApplyWithLaws_tilt (ell := ell) μ r (C v) Θ ζ (K v) (idealSlotAverage f) b

theorem idealTiltCoefficient_difference
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (r : ∀ j, P j → ℝ) (C : J → Finset (Fin k))
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (a b : MarkedPhysicalMarking P (k+ell)) (aux : GiantTwoSidedPatternAuxiliary P C) :
    K a b aux * (idealFreshTargetMass r C b : ℂ) - K a b aux =
      K a b aux * ((idealFreshTargetMass r C b - 1 : ℝ) : ℂ) := by
  push_cast
  ring

theorem idealTiltCoefficient_difference_norm
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (r : ∀ j, P j → ℝ) (hr : ∀ j p, 1 ≤ r j p)
    (C : J → Finset (Fin k)) (K : GiantTwoSidedPatternCoefficient P C ell)
    (T : ℝ) (hT : ∀ b : MarkedPhysicalMarking P (k+ell), idealFreshTargetMass r C b ≤ T)
    (a b : MarkedPhysicalMarking P (k+ell)) (aux : GiantTwoSidedPatternAuxiliary P C) :
    ‖K a b aux * (idealFreshTargetMass r C b : ℂ) - K a b aux‖ ≤
      ‖K a b aux‖ * (T - 1) := by
  rw [idealTiltCoefficient_difference, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (idealFreshTargetMass_one_le r hr C b))]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hT b) 1) (norm_nonneg _)

end
end ArtinMatthews
