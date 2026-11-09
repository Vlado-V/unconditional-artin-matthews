module

public import ArtinMatthews.GiantSignedFiniteFourier
public import ArtinMatthews.IdealLabelOperator


set_option backward.privateInPublic true
@[expose] public section

/-! The clean residue lift retains the complete residual ideal operator.
Each residue character gives its actual shifted real frequency. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedCharacterPhase_idealPhase
    {G : Type*} [AddCommGroup G] [Fintype G]
    (χ : AddChar G ℂ) (u : G) (Θ : ℝ) (D : ℕ) :
    idealAdditivePhase Θ D * χ (D • u) =
      idealAdditivePhase (Θ + giantSignedCharacterPhase χ u) D := by
  have hc := giantSignedCharacterPhase_zsmul χ u (D : ℤ)
  simp only [natCast_zsmul, Int.cast_natCast] at hc
  rw [hc, idealAdditivePhase, idealAdditivePhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

def giantSignedCleanFiberPattern {G J : Type*} [AddCommGroup G]
    [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, P j → ℝ) (C : J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (u : G)
    (f : G → MarkedPhysicalMarking P (k+ell) → ℂ)
    (x : G) (a : MarkedPhysicalMarking P (k+ell)) : ℂ := by
  classical
  exact ∑ aux : GiantTwoSidedPatternAuxiliary P C,
    (idealAuxiliaryMass auxLaw aux : ℂ) *
      ∑ b : MarkedPhysicalMarking P (k+ell), if IdealCopied C a b then
        let D := giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux
        (idealFreshTargetMass freshLaw C b : ℂ) * K a b aux *
          (D : ℂ) ^ ((ζ : ℂ) * Complex.I) * idealAdditivePhase Θ D * f (x + D • u) b
      else 0

theorem giantSignedCleanFiberPattern_character
    {G J : Type*} [AddCommGroup G] [Fintype G] [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, P j → ℝ) (C : J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (u x : G) (χ : AddChar G ℂ)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    giantSignedCleanFiberPattern freshLaw auxLaw C Θ ζ K u
      (fun y b => χ y * f b) x a =
      χ x * idealPatternApplyWithLaws freshLaw auxLaw C
        (Θ + giantSignedCharacterPhase χ u) ζ K f a := by
  classical
  unfold giantSignedCleanFiberPattern idealPatternApplyWithLaws
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro aux _
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with h
  · dsimp only
    rw [AddChar.map_add_eq_mul]
    have hp := giantSignedCharacterPhase_idealPhase χ u Θ
      (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux)
    calc
      _ = χ x * (idealAuxiliaryMass auxLaw aux : ℂ) *
          ((idealFreshTargetMass freshLaw C b : ℂ) * K a b aux *
            ((giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux : ℕ) : ℂ) ^
              ((ζ : ℂ) * Complex.I) *
            (idealAdditivePhase Θ
              (giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux) *
              χ ((giantTwoSidedPatternCopiedProduct C a * giantTwoSidedPatternAuxiliaryProduct aux) • u)) * f b) := by ring
      _ = _ := by rw [hp]; ring
  · ring

private theorem idealSlotAverage_const_mul {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} (c : ℂ) (f : MarkedPhysicalMarking P M → ℂ)
    (a : MarkedPhysicalMarking P M) :
    idealSlotAverage (fun b => c * f b) a = c * idealSlotAverage f a := by
  unfold idealSlotAverage
  rw [← Finset.mul_sum]
  ring

def giantSignedCleanFiberApply {I G J : Type*} [AddCommGroup G]
    [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ ν, GiantTwoSidedPatternCoefficient P (C ν) ell) (u : G)
    (f : G → MarkedPhysicalMarking P (k+ell) → ℂ)
    (x : G) : MarkedPhysicalMarking P (k+ell) → ℂ :=
  idealSlotAverage (fun a => ∑ ν ∈ patterns,
    giantSignedCleanFiberPattern freshLaw auxLaw (C ν) Θ ζ (K ν) u
      (fun y => idealSlotAverage (f y)) x a)

theorem giantSignedCleanFiberApply_character
    {I G J : Type*} [AddCommGroup G] [Fintype G] [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ ν, GiantTwoSidedPatternCoefficient P (C ν) ell) (u x : G) (χ : AddChar G ℂ)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    giantSignedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K u
      (fun y b => χ y * f b) x a =
      χ x * idealOperatorWithLaws freshLaw auxLaw patterns C
        (Θ + giantSignedCharacterPhase χ u) ζ K f a := by
  classical
  unfold giantSignedCleanFiberApply idealOperatorWithLaws
  have hi (y : G) : idealSlotAverage (fun b => χ y * f b) =
      fun b => χ y * idealSlotAverage f b := by
    funext b
    exact idealSlotAverage_const_mul (χ y) f b
  simp_rw [hi, giantSignedCleanFiberPattern_character]
  simp_rw [← Finset.mul_sum]
  exact idealSlotAverage_const_mul (χ x) _ a

end
end ArtinMatthews
