module

public import ArtinMatthews.IdealPatternRowExpectation


set_option backward.privateInPublic true
@[expose] public section

/-! The original ideal row is an expectation over the full target
product law, with copied slots filled from the source exactly. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealPattern_target_sum_eq_mix {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (C : G → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell))
    (F : MarkedPhysicalMarking P (k+ell) → ℂ) :
    (∑ b : MarkedPhysicalMarking P (k+ell),if IdealCopied C a b then
      (idealFreshTargetMass (fun g => markedHarmonicAtom (P g)) C b:ℂ)*F b else 0)=
      idealLabelExpectation P (k+ell)
        (fun x => F (idealMix (idealPatternFreeCoordinates C) a x)) := by
  let S := idealPatternFreeCoordinates (ell:=ell) C
  have hfill (x : MarkedPhysicalMarking P (k+ell)) :
      idealFlattenLabels.symm (finiteProductFill S (idealFlattenLabels a) (idealFullSelectedLabels S x))=
        idealMix S a x := by
    funext g i
    dsimp only [idealFlattenLabels,Equiv.coe_fn_symm_mk,finiteProductFill,idealFullSelectedLabels,idealMix]
    split_ifs <;> rfl
  rw [idealPattern_target_sum_eq_fresh]
  have hm := idealFullSelected_marginal P hV S
    (fun y => F (idealFlattenLabels.symm (finiteProductFill S (idealFlattenLabels a) y)))
  calc
    _ = ∑ y : IdealSelectedLabels (idealFullSelectedBands P S),
        (idealSelectedMass (idealFullSelectedBands P S) y:ℂ)*
          F (idealFlattenLabels.symm (finiteProductFill S (idealFlattenLabels a) y)) := by
      refine sum_congr ?_ ?_
      · ext y
        exact ⟨fun _ => mem_univ y,fun _ => mem_univ y⟩
      · intro y _
        unfold finiteProductMarginalMass idealSelectedMass idealFullSelectedBands
        rw [Complex.ofReal_prod]
    _ = idealLabelExpectation P (k+ell)
        (fun x => F (idealFlattenLabels.symm (finiteProductFill S (idealFlattenLabels a) (idealFullSelectedLabels S x)))) := hm.symm
    _ = _ := by
      apply congrArg (idealLabelExpectation P (k+ell))
      funext x
      rw [hfill]

theorem idealPatternApply_expectation {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (C : G → Finset (Fin k)) (Θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealPatternApplyWithLaws (fun g => markedHarmonicAtom (P g))
      (fun g => markedHarmonicAtom (P g)) C Θ ζ K f a=
      ∑ aux : GiantTwoSidedPatternAuxiliary P C,
        (giantTwoSidedPatternAuxiliaryMass aux:ℂ)*
          idealLabelExpectation P (k+ell) (fun x =>
            K a (idealMix (idealPatternFreeCoordinates C) a x) aux*
            ((giantTwoSidedPatternCopiedProduct C a*giantTwoSidedPatternAuxiliaryProduct aux:ℕ):ℂ)^
              ((ζ:ℂ)*Complex.I)*
            idealAdditivePhase Θ (giantTwoSidedPatternCopiedProduct C a*giantTwoSidedPatternAuxiliaryProduct aux)*
            f (idealMix (idealPatternFreeCoordinates C) a x)) := by
  unfold idealPatternApplyWithLaws
  apply sum_congr rfl
  intro aux _
  change (giantTwoSidedPatternAuxiliaryMass aux:ℂ)*_= _
  congr 1
  simpa only [mul_assoc] using idealPattern_target_sum_eq_mix P hV C a
    (fun b => K a b aux*
      ((giantTwoSidedPatternCopiedProduct C a*giantTwoSidedPatternAuxiliaryProduct aux:ℕ):ℂ)^
        ((ζ:ℂ)*Complex.I)*
      idealAdditivePhase Θ (giantTwoSidedPatternCopiedProduct C a*giantTwoSidedPatternAuxiliaryProduct aux)*f b)

end
end ArtinMatthews
