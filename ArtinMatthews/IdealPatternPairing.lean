module

public import ArtinMatthews.IdealPatternExpectation
public import ArtinMatthews.IdealLabelPairing
public import ArtinMatthews.IdealProductSwap
public import ArtinMatthews.IdealPatternProducts


set_option backward.privateInPublic true
@[expose] public section

/-! Pairing the actual copied/fresh row gives its literal auxiliary
average and two full product-label expectations. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealPatternPairing_expectation {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (C : G → Finset (Fin k)) (Θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient P C ell)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelPairing P f (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
      (fun j => markedHarmonicAtom (P j)) C Θ ζ K g)=
      ∑ aux : GiantTwoSidedPatternAuxiliary P C,(giantTwoSidedPatternAuxiliaryMass aux:ℂ)*
        idealLabelExpectation P (k+ell) (fun a => idealLabelExpectation P (k+ell) (fun b =>
          star (f a)*K a (idealMix (idealPatternFreeCoordinates C) a b) aux*
            idealDilationPhase Θ ζ (giantTwoSidedPatternCopiedProduct C a*giantTwoSidedPatternAuxiliaryProduct aux)*
            g (idealMix (idealPatternFreeCoordinates C) a b))) := by
  unfold idealLabelPairing
  simp_rw [idealPatternApply_expectation P hV]
  unfold idealLabelExpectation idealDilationPhase
  simp only [mul_sum,RCLike.algebraMap_eq_ofReal]
  rw [sum_comm]
  apply sum_congr rfl
  intro aux _
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  have hcast (r : ℝ) : (RCLike.ofReal r : ℂ)=Complex.ofReal r := rfl
  simp only [hcast]
  ring

end
end ArtinMatthews
