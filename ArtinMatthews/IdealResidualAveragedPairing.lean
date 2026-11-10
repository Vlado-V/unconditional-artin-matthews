module

public import ArtinMatthews.IdealCellPhaseComparison
public import ArtinMatthews.IdealLabelPairing
public import ArtinMatthews.IdealPatternFreeCoordinates
public import ArtinMatthews.IdealResidualFamily
public import ArtinMatthews.IdealAverageComposition
public import ArtinMatthews.IdealAveragePairing
public import ArtinMatthews.IdealProbeAverages
public import ArtinMatthews.IdealResidualAverages
public import ArtinMatthews.IdealResidualPairing
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrary full-tuple tests enter each literal comparison through
the two prescribed coordinate averages. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealResidualPattern_pairing_averages {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (hP : ∀ g p,p∈P g → 0 < p) (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (Q : ℕ) (h ξ Θ ζ : ℝ) (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelPairing P f (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
      (fun j => markedHarmonicAtom (P j)) (idealResidualCopied (some (A,B))) Θ ζ
      (idealResidualCoefficient P Q h ξ (some (A,B))) g)=
    idealLabelPairing P
      (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) f)
      (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
        (fun j => markedHarmonicAtom (P j)) (idealResidualCopied (some (A,B))) Θ ζ
        (idealResidualCoefficient P Q h ξ (some (A,B)))
        (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots B)) g)) := by
  let T : (MarkedPhysicalMarking P (k+ell) → ℂ) → MarkedPhysicalMarking P (k+ell) → ℂ :=
    idealPatternApplyWithLaws (ell:=ell) (fun j => markedHarmonicAtom (P j))
    (fun j => markedHarmonicAtom (P j)) (idealResidualCopied (some (A,B))) Θ ζ
    (idealResidualCoefficient P Q h ξ (some (A,B)))
  have hT : idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) (T g)=T g :=
    idealAverageSet_of_independent P hV _ (T g)
      (idealResidualPattern_input_independent P A B hAB Q h ξ Θ ζ g)
  have htarget : T (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots B)) g)=T g := by
    funext a
    exact idealResidualPattern_target_average P hV hP A B hAB Q h ξ Θ ζ g a
  change idealLabelPairing P f (T g)=idealLabelPairing P
    (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) f)
      (T (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots B)) g))
  rw [htarget,idealLabelPairing_average_adjoint,hT]

theorem idealResidualPattern_full_pairing_cells {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hP : ∀ j p,p∈P j → 0 < p) (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (Q : ℕ) (h ξ Θ ζ : ℝ) (f g : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelPairing P f (idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j))
      (fun j => markedHarmonicAtom (P j)) (idealResidualCopied (some (A,B))) Θ ζ
      (idealResidualCoefficient P Q h ξ (some (A,B))) g)=
    idealLabelExpectation P (k+ell) (fun a =>
      star (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) f a)*
      (-(-1:ℂ)^(A.card+B.card)*
        (giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a:ℂ)^((ζ:ℂ)*Complex.I)*
        idealFullCellPhaseAverage (idealResidualBands P A) (idealResidualBands P B) Q h ξ ζ
          (Θ*(giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a:ℝ))
          (idealResidualSelectedMarking A a) (idealResidualSelectedMarking B a))*
      idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots B)) g a) := by
  rw [idealResidualPattern_pairing_averages P hV hP A B hAB Q h ξ Θ ζ]
  exact idealResidualPattern_pairing_cells P hV A B hAB Q h ξ Θ ζ _ _
    (idealAverageSet_mix P _ f) (idealAverageSet_mix P _ g)

end
end ArtinMatthews
