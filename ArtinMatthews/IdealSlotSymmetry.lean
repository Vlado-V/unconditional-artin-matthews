module

public import ArtinMatthews.IdealLabelOperator
public import ArtinMatthews.IdealProductSymmetry


set_option backward.privateInPublic true
@[expose] public section

/-! The literal endpoint slot averages are symmetric contractions for
the full harmonic product measure. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealSlotAverage_symmetric {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {M : ℕ} (f : MarkedPhysicalMarking P M → ℂ) :
    IdealSymmetric (idealSlotAverage f) := by
  intro ρ a
  unfold idealSlotAverage
  congr 1
  have hcomp (π : J → Equiv.Perm (Fin M)) :
      giantTwoSidedPermuteLabels π (giantTwoSidedPermuteLabels ρ a)=
        giantTwoSidedPermuteLabels (ρ*π) a := by
    funext j i
    rfl
  simp_rw [hcomp]
  exact Equiv.sum_comp (Equiv.mulLeft ρ) (fun π => f (giantTwoSidedPermuteLabels π a))

theorem idealLabelEnergy_permute {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (f : MarkedPhysicalMarking P M → ℂ)
    (π : J → Equiv.Perm (Fin M)) :
    idealLabelEnergy P M (fun a => f (giantTwoSidedPermuteLabels π a))=idealLabelEnergy P M f := by
  have h := Equiv.sum_comp (idealLabelPermutation (P:=P) π)
    (fun a => idealLabelMass P M a*‖f a‖^2)
  simpa only [idealLabelEnergy,idealLabelPermutation,Equiv.coe_fn_mk,idealLabelMass_permute] using h

theorem idealSlotAverage_energy_le {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (f : MarkedPhysicalMarking P M → ℂ) :
    idealLabelEnergy P M (idealSlotAverage f) ≤ idealLabelEnergy P M f := by
  let W : ℝ := (Fintype.card (J → Equiv.Perm (Fin M)):ℝ)⁻¹
  have hn : 0 < (Fintype.card (J → Equiv.Perm (Fin M)):ℝ) := by exact_mod_cast Fintype.card_pos
  have hW : 0 ≤ W := inv_nonneg.mpr hn.le
  have hsum : (∑ _π : J → Equiv.Perm (Fin M),W)=1 := by
    simp only [sum_const,nsmul_eq_mul,W]
    exact mul_inv_cancel₀ hn.ne'
  have hq (a : MarkedPhysicalMarking P M) :
      idealSlotAverage f a=∑ π : J → Equiv.Perm (Fin M),(W:ℂ)*f (giantTwoSidedPermuteLabels π a) := by
    simp only [idealSlotAverage,W,Complex.ofReal_inv,Complex.ofReal_natCast,mul_sum]
  have hj (a : MarkedPhysicalMarking P M) : ‖idealSlotAverage f a‖^2 ≤
      ∑ π : J → Equiv.Perm (Fin M),W*‖f (giantTwoSidedPermuteLabels π a)‖^2 := by
    rw [hq]
    exact idealWeightedJensen (fun _ => W) (fun _ => hW) hsum _
  calc
    _ ≤ ∑ a,idealLabelMass P M a*∑ π : J → Equiv.Perm (Fin M),
        W*‖f (giantTwoSidedPermuteLabels π a)‖^2 :=
      sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hj a) (idealLabelMass_nonneg P M hV a)
    _ = ∑ π : J → Equiv.Perm (Fin M),
        W*idealLabelEnergy P M (fun a => f (giantTwoSidedPermuteLabels π a)) := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro π _
      unfold idealLabelEnergy
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      ring
    _ = _ := by
      simp_rw [idealLabelEnergy_permute]
      rw [← sum_mul,hsum,one_mul]

theorem idealOperatorWithLaws_symmetric {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ}
    (freshLaw auxLaw : ∀ j,↥(P j) → ℝ) (patterns : Finset I)
    (C : I → J → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ ν,GiantTwoSidedPatternCoefficient P (C ν) ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    IdealSymmetric (idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ K f) :=
  idealSlotAverage_symmetric _

end
end ArtinMatthews
