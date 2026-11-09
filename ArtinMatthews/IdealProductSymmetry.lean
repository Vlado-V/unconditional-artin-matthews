module

public import ArtinMatthews.IdealProductBasis


set_option backward.privateInPublic true
@[expose] public section

/-! Independent slot permutations preserve the actual product mass and
act identically on the finite Hoeffding transform. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable

def idealLabelPermutation {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (π : J → Equiv.Perm (Fin M)) : MarkedPhysicalMarking P M ≃ MarkedPhysicalMarking P M where
  toFun := giantTwoSidedPermuteLabels π
  invFun := giantTwoSidedPermuteLabels (fun j => (π j).symm)
  left_inv a := by funext j i; simp [giantTwoSidedPermuteLabels]
  right_inv a := by funext j i; simp [giantTwoSidedPermuteLabels]

theorem idealLabelMass_permute {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M : ℕ} (π : J → Equiv.Perm (Fin M))
    (a : MarkedPhysicalMarking P M) :
    idealLabelMass P M (giantTwoSidedPermuteLabels π a)=idealLabelMass P M a := by
  unfold idealLabelMass giantTwoSidedPermuteLabels
  apply prod_congr rfl
  intro j _
  exact Equiv.prod_comp (π j) (fun i => markedHarmonicAtom (P j) (a j i))

theorem idealProductBasisVector_permute {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ}
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (π : J → Equiv.Perm (Fin M)) (t a : MarkedPhysicalMarking P M) :
    idealProductBasisVector b (giantTwoSidedPermuteLabels π t)
      (giantTwoSidedPermuteLabels π a)=idealProductBasisVector b t a := by
  change (∏ j,∏ i,b j (t j (π j i)) (a j (π j i)))=∏ j,∏ i,b j (t j i) (a j i)
  apply prod_congr rfl
  intro j _
  exact Equiv.prod_comp (π j) (fun i => b j (t j i) (a j i))

theorem idealHoeffdingTransform_symmetric {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ}
    (b : ∀ j,OrthonormalBasis ↥(P j) ℂ (EuclideanSpace ℂ ↥(P j)))
    (f : MarkedPhysicalMarking P M → ℂ) (hf : IdealSymmetric f) :
    IdealSymmetric (idealHoeffdingTransform P b f) := by
  intro π t
  unfold idealHoeffdingTransform
  rw [(idealProductBasis b).repr_apply_apply,(idealProductBasis b).repr_apply_apply]
  rw [idealProductBasis_apply,idealProductBasis_apply]
  change (∑ a,idealWeightedVector P f a * star (idealProductBasisVector b
    (giantTwoSidedPermuteLabels π t) a))=
    ∑ a,idealWeightedVector P f a * star (idealProductBasisVector b t a)
  rw [← (idealLabelPermutation (P:=P) π).sum_comp
    (fun a => idealWeightedVector P f a * star (idealProductBasisVector b
      (giantTwoSidedPermuteLabels π t) a))]
  apply sum_congr rfl
  intro a _
  change idealWeightedVector P f (giantTwoSidedPermuteLabels π a) *
    star (idealProductBasisVector b (giantTwoSidedPermuteLabels π t)
      (giantTwoSidedPermuteLabels π a))=_
  rw [idealProductBasisVector_permute]
  change (Real.sqrt (idealLabelMass P M (giantTwoSidedPermuteLabels π a)):ℂ)*
    f (giantTwoSidedPermuteLabels π a)*_=_
  rw [idealLabelMass_permute,hf]
  rfl

end
end ArtinMatthews
