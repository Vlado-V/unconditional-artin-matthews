module

public import ArtinMatthews.IdealResidualAveragedPairing
public import ArtinMatthews.IdealResidualHeadKernel
public import ArtinMatthews.IdealRawPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The actual comparison error retains its sign, shared phase and
original coordinate averages before passing to the head-label law. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealRawPairing_expectation {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (Θ ζ : ℝ)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealRawPairing P Θ ζ f g=idealLabelExpectation P (k+ell)
      (fun a => star (f a)*g a*idealRawPhase Θ ζ a) := by
  unfold idealRawPairing idealLabelPairing idealLabelExpectation
  simp only [Complex.coe_algebraMap]
  apply sum_congr rfl
  intro a _
  ring

theorem idealResidualHeadKernel_from_full {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (Q : ℕ) (h ξ Θ ζ : ℝ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealResidualHeadKernel P A B Q h ξ Θ ζ (idealLabelHead a)
      (idealResidualSelectedMarking A a) (idealResidualSelectedMarking B a)=
    idealRawPhase Θ ζ a-
      (giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a:ℂ)^((ζ:ℂ)*Complex.I)*
        idealFullCellPhaseAverage (idealResidualBands P A) (idealResidualBands P B) Q h ξ ζ
          (Θ*(giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a:ℝ))
          (idealResidualSelectedMarking A a) (idealResidualSelectedMarking B a) := by
  unfold idealResidualHeadKernel
  simp only [← idealCopiedProduct_head (idealResidualFreeSlots (A ∪ B)) a]
  rw [idealRawPhase_selected P A B hAB]
  ring

def idealResidualFullError {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (A B : Finset (G × Fin k))
    (Q : ℕ) (h ξ Θ ζ : ℝ) (f g : MarkedPhysicalMarking P (k+ell) → ℂ) : ℂ :=
  idealLabelExpectation P (k+ell) (fun a =>
    star (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) f a)*
      idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots B)) g a*
      idealResidualHeadKernel P A B Q h ξ Θ ζ (idealLabelHead a)
        (idealResidualSelectedMarking A a) (idealResidualSelectedMarking B a))

theorem idealResidualPattern_error_full {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hP : ∀ j p,p∈P j → 0 < p) (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (Q : ℕ) (h ξ Θ ζ : ℝ) (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelPairing P f (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
      (fun j => markedHarmonicAtom (P j)) (idealResidualCopied (some (A,B))) Θ ζ
      (idealResidualCoefficient P Q h ξ (some (A,B))) g)+
    (-1:ℂ)^(A.card+B.card)*idealRawPairing P Θ ζ
      (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) f)
      (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots B)) g)=
    (-1:ℂ)^(A.card+B.card)*idealResidualFullError P A B Q h ξ Θ ζ f g := by
  rw [idealResidualPattern_full_pairing_cells P hV hP A B hAB Q h ξ Θ ζ f g,
    idealRawPairing_expectation]
  unfold idealResidualFullError idealLabelExpectation
  simp only [mul_sum,Complex.coe_algebraMap]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  rw [idealResidualHeadKernel_from_full P A B hAB]
  ring

theorem idealResidualFullError_head {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (A B : Finset (G × Fin k)) (Q : ℕ) (h ξ Θ ζ : ℝ)
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealResidualFullError P A B Q h ξ Θ ζ f g=
      idealLabelExpectation P k (fun a =>
        star (idealAverageSet P A (idealHeadTest P f) a)*idealAverageSet P B (idealHeadTest P g) a*
          idealResidualHeadKernel P A B Q h ξ Θ ζ a (idealFullSelectedLabels A a) (idealFullSelectedLabels B a)) := by
  let F : MarkedPhysicalMarking P k → ℂ := fun a =>
    star (idealAverageSet P A (idealHeadTest P f) a)*
      idealAverageSet P B (idealHeadTest P g) a*
      idealResidualHeadKernel P A B Q h ξ Θ ζ a
        (idealFullSelectedLabels A a) (idealFullSelectedLabels B a)
  unfold idealResidualFullError
  calc
    _ = idealLabelExpectation P (k+ell) (fun a =>
        star (idealAverageSet P A (idealHeadTest P f) (idealLabelHead a))*
          idealAverageSet P B (idealHeadTest P g) (idealLabelHead a)*
          idealResidualHeadKernel P A B Q h ξ Θ ζ (idealLabelHead a)
            (idealFullSelectedLabels A (idealLabelHead a)) (idealFullSelectedLabels B (idealLabelHead a))) := by
      apply congrArg (idealLabelExpectation P (k+ell))
      funext a
      rw [idealHead_free_average,idealHead_free_average]
      rfl
    _ = _ := by
      change idealLabelExpectation P (k+ell) (fun a => F (idealLabelHead a)) =
        idealLabelExpectation P k F
      exact idealHead_expectation (A:=ℂ) (k:=k) (ell:=ell) P hV F

theorem idealResidualPattern_error_eq {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hP : ∀ j p,p∈P j → 0 < p) (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (Q : ℕ) (h ξ Θ ζ : ℝ) (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelPairing P f (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
      (fun j => markedHarmonicAtom (P j)) (idealResidualCopied (some (A,B))) Θ ζ
      (idealResidualCoefficient P Q h ξ (some (A,B))) g)+
    (-1:ℂ)^(A.card+B.card)*idealRawPairing P Θ ζ
      (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) f)
      (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots B)) g)=
    (-1:ℂ)^(A.card+B.card)*idealLabelExpectation P k (fun a =>
      star (idealAverageSet P A (idealHeadTest P f) a)*idealAverageSet P B (idealHeadTest P g) a*
        idealResidualHeadKernel P A B Q h ξ Θ ζ a (idealFullSelectedLabels A a) (idealFullSelectedLabels B a)) := by
  rw [idealResidualPattern_error_full P hV hP A B hAB,idealResidualFullError_head P hV]

theorem idealResidualPattern_error_bound {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hP : ∀ j p,p∈P j → 0 < p) (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (Q : ℕ) (h ξ Θ ζ : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hcmp : ∀ α u v,‖idealSelectedComparisonForm (idealResidualBands P A) (idealResidualBands P B)
      Q h ξ ζ α u v‖ ≤ ε*Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P A)) u)*
        Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P B)) v))
    (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    ‖idealLabelPairing P f (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
      (fun j => markedHarmonicAtom (P j)) (idealResidualCopied (some (A,B))) Θ ζ
      (idealResidualCoefficient P Q h ξ (some (A,B))) g)+
    (-1:ℂ)^(A.card+B.card)*idealRawPairing P Θ ζ
      (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) f)
      (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots B)) g)‖ ≤
      ε*idealLabelNorm P f*idealLabelNorm P g := by
  rw [idealResidualPattern_error_eq P hV hP A B hAB Q h ξ Θ ζ f g,norm_mul]
  have hs : ‖(-1:ℂ)^(A.card+B.card)‖=1 := by simp
  rw [hs,one_mul]
  have hb := idealResidualHeadKernel_bound P hV hP A B hAB Q h ξ Θ ζ hε hcmp
    (idealAverageSet P A (idealHeadTest P f)) (idealAverageSet P B (idealHeadTest P g))
    (idealAverageSet_mix P A (idealHeadTest P f)) (idealAverageSet_mix P B (idealHeadTest P g))
  have hf := (idealAverageSet_energy_le P hV A (idealHeadTest P f)).trans (idealHeadTest_energy_le P hV f)
  have hg := (idealAverageSet_energy_le P hV B (idealHeadTest P g)).trans (idealHeadTest_energy_le P hV g)
  exact hb.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hf) hε) (Real.sqrt_le_sqrt hg)
    (Real.sqrt_nonneg _) (mul_nonneg hε (Real.sqrt_nonneg _)))

end
end ArtinMatthews
