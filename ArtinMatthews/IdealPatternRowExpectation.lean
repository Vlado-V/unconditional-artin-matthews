module

public import ArtinMatthews.IdealPatternFreeCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! The original unweighted target-state sum is exactly the product
law of fresh coordinates with every copied coordinate fixed. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealPattern_target_sum_eq_fresh {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ} (law : ∀ j,↥(P j) → ℝ)
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell))
    (F : MarkedPhysicalMarking P (k+ell) → ℂ) :
    (∑ b : MarkedPhysicalMarking P (k+ell),if IdealCopied C a b then
      (idealFreshTargetMass law C b:ℂ)*F b else 0)=
      ∑ y : ∀ v : ↥(idealPatternFreeCoordinates C),↥(P v.val.1),
        finiteProductMarginalMass (fun v : ↥(idealPatternFreeCoordinates C) => fun p => (law v.val.1 p:ℂ)) y*
          F (idealFlattenLabels.symm (finiteProductFill (idealPatternFreeCoordinates C) (idealFlattenLabels a) y)) := by
  let w : ∀ v : J × Fin (k+ell),↥(P v.1) → ℂ := fun v p => (law v.1 p:ℂ)
  have hm (b : MarkedPhysicalMarking P (k+ell)) :
      finiteProductMarginalMass (fun v : ↥(idealPatternFreeCoordinates (ell:=ell) C) => w v.val)
        (finiteProductRestriction (idealPatternFreeCoordinates C) (idealFlattenLabels b))=
        (idealFreshTargetMass law C b:ℂ) := by
    unfold finiteProductMarginalMass w
    rw [← Complex.ofReal_prod]
    exact congrArg (fun r : ℝ => (r:ℂ)) (idealPatternFreshMass_eq_restricted law C b)
  calc
    _ = ∑ x : ∀ v : J × Fin (k+ell),↥(P v.1),
        if ∀ v,v∉idealPatternFreeCoordinates C → x v=idealFlattenLabels a v then
          finiteProductMarginalMass (fun v : ↥(idealPatternFreeCoordinates (ell:=ell) C) => w v.val)
            (finiteProductRestriction (idealPatternFreeCoordinates C) x)*F (idealFlattenLabels.symm x)
        else 0 := by
      rw [← (idealFlattenLabels (P:=P) (M:=k+ell)).sum_comp]
      apply sum_congr rfl
      intro b _
      rw [hm]
      simp only [Equiv.symm_apply_apply,← idealCopied_iff_freeComplement]
    _ = _ := by
      have he := finiteProductFixedComplement_sum w (idealPatternFreeCoordinates C) (idealFlattenLabels a)
        (fun x => F (idealFlattenLabels.symm x))
      refine Eq.trans ?_ he
      apply sum_congr rfl
      intro x _
      split_ifs <;> rfl

end
end ArtinMatthews
