module

public import ArtinMatthews.IdealPatternPairing
public import ArtinMatthews.IdealResidualSwap
public import ArtinMatthews.IdealResidualAuxiliaryAverage


set_option backward.privateInPublic true
@[expose] public section

/-! The actual comparison pattern, on tests independent of the freed
probes, is the full diagonal character-cell phase average. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealResidualPattern_pairing_diagonal {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (A B : Finset (G × Fin k)) (hAB : Disjoint A B) (Q : ℕ) (h ξ Θ ζ : ℝ)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ)
    (hf : ∀ a b,f (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) a b)=f a)
    (hg : ∀ a b,g (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots B)) a b)=g a) :
    idealLabelPairing P f (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
      (fun j => markedHarmonicAtom (P j)) (idealResidualCopied (some (A,B))) Θ ζ
      (idealResidualCoefficient P Q h ξ (some (A,B))) g)=
      ∑ aux : GiantTwoSidedPatternAuxiliary P (idealResidualFreeSlots (A ∪ B)),
        (giantTwoSidedPatternAuxiliaryMass aux:ℂ)*idealLabelExpectation P (k+ell)
          (fun a => star (f a)*idealResidualCoefficient P Q h ξ (some (A,B)) a a aux*
            idealDilationPhase Θ ζ (giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a*
              giantTwoSidedPatternAuxiliaryProduct aux)*g a) := by
  rw [idealPatternPairing_expectation P hV]
  apply sum_congr rfl
  intro aux _
  change GiantTwoSidedPatternAuxiliary P (idealResidualFreeSlots (A ∪ B)) at aux
  congr 1
  let F := fun (a b : MarkedPhysicalMarking P (k+ell)) =>
    star (f a)*idealResidualCoefficient P Q h ξ (some (A,B)) a
      (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots (A ∪ B))) a b) aux*
    idealDilationPhase Θ ζ (giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a*
      giantTwoSidedPatternAuxiliaryProduct aux)*
    g (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots (A ∪ B))) a b)
  change idealLabelExpectation P (k+ell) (fun a => idealLabelExpectation P (k+ell) (F a))= _
  rw [← idealLabelExpectation_swap P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) F]
  apply congrArg (idealLabelExpectation P (k+ell))
  funext a
  have hp (b : MarkedPhysicalMarking P (k+ell)) :
      F (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) a b)
        (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) b a)=
      star (f a)*idealResidualCoefficient P Q h ξ (some (A,B)) a a aux*
        idealDilationPhase Θ ζ (giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a*
          giantTwoSidedPatternAuxiliaryProduct aux)*g a := by
    dsimp only [F]
    rw [hf,idealResidualSwap_coefficient P A B hAB,idealResidualSwap_copied,
      idealResidualSwap_target_function A B g hg]
  simp_rw [hp]
  unfold idealLabelExpectation
  rw [← sum_mul,← map_sum,idealLabelMass_sum P (k+ell) hV,map_one,one_mul]

theorem idealResidualPattern_pairing_cells {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (A B : Finset (G × Fin k)) (hAB : Disjoint A B) (Q : ℕ) (h ξ Θ ζ : ℝ)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ)
    (hf : ∀ a b,f (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) a b)=f a)
    (hg : ∀ a b,g (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots B)) a b)=g a) :
    idealLabelPairing P f (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
      (fun j => markedHarmonicAtom (P j)) (idealResidualCopied (some (A,B))) Θ ζ
      (idealResidualCoefficient P Q h ξ (some (A,B))) g)=
    idealLabelExpectation P (k+ell) (fun a => star (f a)*
      (-(-1:ℂ)^(A.card+B.card)*
        (giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a:ℂ)^((ζ:ℂ)*Complex.I)*
        idealFullCellPhaseAverage (idealResidualBands P A) (idealResidualBands P B) Q h ξ ζ
          (Θ*(giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a:ℝ))
          (idealResidualSelectedMarking A a) (idealResidualSelectedMarking B a))*g a) := by
  rw [idealResidualPattern_pairing_diagonal P hV A B hAB Q h ξ Θ ζ f g hf hg]
  calc
    _ = idealLabelExpectation P (k+ell) (fun a => star (f a)*
        (∑ aux : GiantTwoSidedPatternAuxiliary P (idealResidualFreeSlots (A ∪ B)),
          (giantTwoSidedPatternAuxiliaryMass aux:ℂ)*
            idealResidualCoefficient P Q h ξ (some (A,B)) a a aux*
            idealDilationPhase Θ ζ (giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a*
              giantTwoSidedPatternAuxiliaryProduct aux))*g a) := by
      unfold idealLabelExpectation
      simp only [mul_sum,sum_mul,Complex.coe_algebraMap]
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro aux _
      ring
    _ = _ := by
      apply congrArg (idealLabelExpectation P (k+ell))
      funext a
      rw [idealResidual_auxiliary_average P A B hAB]

end
end ArtinMatthews
