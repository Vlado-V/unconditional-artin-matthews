module

public import ArtinMatthews.IdealLabelOperator


set_option backward.privateInPublic true
@[expose] public section

/-! Coefficient linearity of the literal copied/fresh ideal operator. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedIdealSlotAverage_sub {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} (f g : MarkedPhysicalMarking P M → ℂ)
    (a : MarkedPhysicalMarking P M) :
    idealSlotAverage (fun b => f b - g b) a = idealSlotAverage f a - idealSlotAverage g a := by
  unfold idealSlotAverage
  rw [Finset.sum_sub_distrib, mul_sub]

theorem giantSignedIdealPattern_sub {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, P j → ℝ) (C : J → Finset (Fin k)) (Θ ζ : ℝ)
    (K L : GiantTwoSidedPatternCoefficient P C ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealPatternApplyWithLaws freshLaw auxLaw C Θ ζ (fun a b aux => K a b aux - L a b aux) f a =
      idealPatternApplyWithLaws freshLaw auxLaw C Θ ζ K f a -
        idealPatternApplyWithLaws freshLaw auxLaw C Θ ζ L f a := by
  classical
  unfold idealPatternApplyWithLaws
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro aux _
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring

theorem giantSignedIdealOperator_sub {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j, P j → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K L : ∀ v, GiantTwoSidedPatternCoefficient P (C v) ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ
        (fun v a b aux => K v a b aux - L v a b aux) f a =
      idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ K f a -
        idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ L f a := by
  classical
  unfold idealOperatorWithLaws
  simp_rw [giantSignedIdealPattern_sub, Finset.sum_sub_distrib]
  exact giantSignedIdealSlotAverage_sub _ _ a

end
end ArtinMatthews
