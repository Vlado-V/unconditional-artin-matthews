module

public import ArtinMatthews.IdealLabelPairing
public import ArtinMatthews.IdealSlotSymmetry


set_option backward.privateInPublic true
@[expose] public section

/-! Both literal endpoint slot averages are retained in the operator
and disappear from a pairing exactly on symmetric tests. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealLabelPairing_sum_right {G I : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (s : Finset I)
    (f : MarkedPhysicalMarking P M → ℂ) (g : I → MarkedPhysicalMarking P M → ℂ) :
    idealLabelPairing P f (fun a => ∑ i∈s,g i a)=∑ i∈s,idealLabelPairing P f (g i) := by
  unfold idealLabelPairing
  simp only [mul_sum]
  rw [sum_comm]

theorem idealLabelPairing_sum_left {G I : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (s : Finset I)
    (f : I → MarkedPhysicalMarking P M → ℂ) (g : MarkedPhysicalMarking P M → ℂ) :
    idealLabelPairing P (fun a => ∑ i∈s,f i a) g=∑ i∈s,idealLabelPairing P (f i) g := by
  unfold idealLabelPairing
  simp only [star_sum,mul_sum,sum_mul]
  rw [sum_comm]

theorem idealLabelPairing_scalar_right {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (c : ℂ) (f g : MarkedPhysicalMarking P M → ℂ) :
    idealLabelPairing P f (fun a => c*g a)=c*idealLabelPairing P f g := by
  unfold idealLabelPairing
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  ring

theorem idealLabelPairing_scalar_left {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (c : ℂ) (f g : MarkedPhysicalMarking P M → ℂ) :
    idealLabelPairing P (fun a => c*f a) g=star c*idealLabelPairing P f g := by
  unfold idealLabelPairing
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  rw [star_mul]
  ring

theorem idealLabelPairing_permute {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (π : G → Equiv.Perm (Fin M))
    (f g : MarkedPhysicalMarking P M → ℂ) :
    idealLabelPairing P (fun a => f (giantTwoSidedPermuteLabels π a))
      (fun a => g (giantTwoSidedPermuteLabels π a))=idealLabelPairing P f g := by
  have h := Equiv.sum_comp (idealLabelPermutation (P:=P) π)
    (fun a => (idealLabelMass P M a:ℂ)*star (f a)*g a)
  simpa only [idealLabelPairing,idealLabelPermutation,Equiv.coe_fn_mk,idealLabelMass_permute] using h

theorem idealLabelPairing_permute_right {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (π : G → Equiv.Perm (Fin M))
    (f g : MarkedPhysicalMarking P M → ℂ) :
    idealLabelPairing P f (fun a => g (giantTwoSidedPermuteLabels π a))=
      idealLabelPairing P (fun a => f (giantTwoSidedPermuteLabels (fun j => (π j).symm) a)) g := by
  have h := idealLabelPairing_permute P π
    (fun a => f (giantTwoSidedPermuteLabels (fun j => (π j).symm) a)) g
  have hi : (fun a => f (giantTwoSidedPermuteLabels (fun j => (π j).symm)
      (giantTwoSidedPermuteLabels π a)))=f := by
    funext a
    congr 1
    funext j i
    exact congrArg (a j) ((π j).apply_symm_apply i)
  rw [hi] at h
  exact h

theorem idealSlotAverage_fixed {G : Type*} [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {M : ℕ} (f : MarkedPhysicalMarking P M → ℂ) (hf : IdealSymmetric f) :
    idealSlotAverage f=f := by
  funext a
  change ((Fintype.card (G → Equiv.Perm (Fin M)):ℂ)⁻¹)*
    (∑ π : G → Equiv.Perm (Fin M),f (giantTwoSidedPermuteLabels π a))=f a
  have hs : (∑ π : G → Equiv.Perm (Fin M),f (giantTwoSidedPermuteLabels π a))=
      (Fintype.card (G → Equiv.Perm (Fin M)):ℂ)*f a := by
    calc
      _ = ∑ _π : G → Equiv.Perm (Fin M),f a := sum_congr rfl fun π _ => hf π a
      _ = _ := by rw [sum_const,nsmul_eq_mul,card_univ]
  rw [hs]
  have hn : (Fintype.card (G → Equiv.Perm (Fin M)):ℂ)≠0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (G → Equiv.Perm (Fin M))≠0)
  rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]

theorem idealSlotAverage_pairing {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (f g : MarkedPhysicalMarking P M → ℂ) :
    idealLabelPairing P f (idealSlotAverage g)=idealLabelPairing P (idealSlotAverage f) g := by
  unfold idealSlotAverage
  rw [idealLabelPairing_scalar_right,idealLabelPairing_sum_right,
    idealLabelPairing_scalar_left,idealLabelPairing_sum_left]
  have hc : star ((Fintype.card (G → Equiv.Perm (Fin M)):ℂ)⁻¹)=
      ((Fintype.card (G → Equiv.Perm (Fin M)):ℂ)⁻¹) := by simp
  rw [hc]
  congr 1
  simp_rw [idealLabelPairing_permute_right]
  have he := Equiv.sum_comp (Equiv.inv (G → Equiv.Perm (Fin M)))
    (fun π : G → Equiv.Perm (Fin M) => idealLabelPairing P
      (fun a => f (giantTwoSidedPermuteLabels π a)) g)
  exact he

theorem idealOperatorWithLaws_pairing {I G : Type*} [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {k ell : ℕ} (freshLaw auxLaw : ∀ g,↥(P g) → ℝ)
    (patterns : Finset I) (C : I → G → Finset (Fin k)) (Θ ζ : ℝ)
    (K : ∀ ν,GiantTwoSidedPatternCoefficient P (C ν) ell)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) (hf : IdealSymmetric f) (hg : IdealSymmetric g) :
    idealLabelPairing P f (idealOperatorWithLaws freshLaw auxLaw patterns C Θ ζ K g)=
      ∑ ν∈patterns,idealLabelPairing P f (idealPatternApplyWithLaws freshLaw auxLaw (C ν) Θ ζ (K ν) g) := by
  unfold idealOperatorWithLaws
  rw [idealSlotAverage_pairing,idealSlotAverage_fixed f hf,idealSlotAverage_fixed g hg]
  exact idealLabelPairing_sum_right P patterns f _

end
end ArtinMatthews
