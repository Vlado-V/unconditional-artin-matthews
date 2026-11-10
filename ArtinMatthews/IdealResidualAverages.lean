module

public import ArtinMatthews.IdealPatternFreeCoordinates
public import ArtinMatthews.IdealResidualFamily
public import ArtinMatthews.IdealAverageComposition
public import ArtinMatthews.IdealAveragePairing
public import ArtinMatthews.IdealPatternExpectation
public import ArtinMatthews.IdealResidualSwap
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

/-! The actual comparison row ignores freed input coordinates and
averages freed target coordinates with their original harmonic law. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealPatternFreeCoordinates_mono {G : Type*} [Fintype G] [DecidableEq G]
    {k ell : ℕ} (C D : G → Finset (Fin k)) (hCD : ∀ g,C g ⊆ D g) :
    idealPatternFreeCoordinates (ell:=ell) C ⊆ idealPatternFreeCoordinates D := by
  intro v hv
  rcases v with ⟨g,i⟩
  induction i using Fin.addCases with
  | left i =>
    exact (idealPatternFreeCoordinates_first D g i).mpr (hCD g ((idealPatternFreeCoordinates_first C g i).mp hv))
  | right i => exact idealPatternFreeCoordinates_tail D g i

theorem idealMix_absorb_left {G : Type*} {P : G → Finset ℕ} {M : ℕ}
    (S T : Finset (G × Fin M)) (hST : S ⊆ T) (a b c : MarkedPhysicalMarking P M) :
    idealMix T (idealMix S a b) c=idealMix T a c := by
  funext g i
  by_cases hT : (g,i)∈T
  · simp only [idealMix,hT,ite_true]
  · have hS : (g,i)∉S := fun h => hT (hST h)
    simp only [idealMix,hT,hS,ite_false]

theorem idealAverageSet_weighted_subset {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (hP : ∀ g p,p∈P g → 0 < p) (S T : Finset (G × Fin M)) (hST : S ⊆ T)
    (H f : MarkedPhysicalMarking P M → ℂ)
    (hH : ∀ a b,H (idealMix S a b)=H a) :
    idealAverageSet P T (fun a => H a*idealAverageSet P S f a)=
      idealAverageSet P T (fun a => H a*f a) := by
  rw [← idealAverageSet_mul_of_independent P S H f hH,
    idealAverageSet_subset_left P hV hP S T hST]

theorem idealResidualCoefficient_target_independent {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (Q : ℕ) (h ξ : ℝ) (a b c : MarkedPhysicalMarking P (k+ell))
    (aux : GiantTwoSidedPatternAuxiliary P (idealResidualFreeSlots (A ∪ B))) :
    idealResidualCoefficient P Q h ξ (some (A,B)) a
      (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots B)) b c) aux=
      idealResidualCoefficient P Q h ξ (some (A,B)) a b aux := by
  dsimp only [idealResidualCoefficient,idealResidualCopied]
  rw [idealResidualSwap_source_selected B A hAB.symm]

theorem idealResidualCoefficient_source_independent {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (Q : ℕ) (h ξ : ℝ) (a b c : MarkedPhysicalMarking P (k+ell))
    (aux : GiantTwoSidedPatternAuxiliary P (idealResidualFreeSlots (A ∪ B))) :
    idealResidualCoefficient P Q h ξ (some (A,B))
      (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) a b) c aux=
      idealResidualCoefficient P Q h ξ (some (A,B)) a c aux := by
  dsimp only [idealResidualCoefficient,idealResidualCopied]
  rw [idealResidualSwap_source_selected A B hAB]

theorem idealPatternApply_source_congr {G : Type*} [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {k ell : ℕ} (freshLaw auxLaw : ∀ j,↥(P j) → ℝ)
    (C : G → Finset (Fin k)) (Θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient P C ell)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a a' : MarkedPhysicalMarking P (k+ell))
    (ha : ∀ j (i : Fin k),i∉C j → a' j (Fin.castAdd ell i)=a j (Fin.castAdd ell i))
    (hK : ∀ b aux,K a' b aux=K a b aux) :
    idealPatternApplyWithLaws freshLaw auxLaw C Θ ζ K f a'=
      idealPatternApplyWithLaws freshLaw auxLaw C Θ ζ K f a := by
  have hc (b : MarkedPhysicalMarking P (k+ell)) : IdealCopied C a' b ↔ IdealCopied C a b := by
    constructor
    · intro h j i hi
      rw [h j i hi,ha j i hi]
    · intro h j i hi
      rw [h j i hi,ha j i hi]
  have hd := giantTwoSidedPatternCopiedProduct_eq ha
  unfold idealPatternApplyWithLaws
  apply sum_congr rfl
  intro aux _
  congr 1
  apply sum_congr rfl
  intro b _
  rw [hc,hK,hd]

theorem idealResidualPattern_input_independent {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ}
    (A B : Finset (G × Fin k)) (hAB : Disjoint A B) (Q : ℕ) (h ξ Θ ζ : ℝ)
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a b : MarkedPhysicalMarking P (k+ell)) :
    idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j)) (fun j => markedHarmonicAtom (P j))
      (idealResidualCopied (some (A,B))) Θ ζ (idealResidualCoefficient P Q h ξ (some (A,B))) f
      (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots A)) a b)=
    idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j)) (fun j => markedHarmonicAtom (P j))
      (idealResidualCopied (some (A,B))) Θ ζ (idealResidualCoefficient P Q h ξ (some (A,B))) f a := by
  apply idealPatternApply_source_congr
  · intro j i hi
    have hA : (j,i)∉A := by
      intro h
      exact hi ((mem_idealResidualFreeSlots (A ∪ B) j i).mpr (mem_union_left B h))
    simp only [idealMix,idealPatternFreeCoordinates_first,mem_idealResidualFreeSlots,hA,ite_false]
  · intro c aux
    exact idealResidualCoefficient_source_independent P A B hAB Q h ξ a b c aux

theorem idealResidualPattern_target_average {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (hP : ∀ g p,p∈P g → 0 < p) (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (Q : ℕ) (h ξ Θ ζ : ℝ) (f : MarkedPhysicalMarking P (k+ell) → ℂ)
    (a : MarkedPhysicalMarking P (k+ell)) :
    idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j)) (fun j => markedHarmonicAtom (P j))
      (idealResidualCopied (some (A,B))) Θ ζ (idealResidualCoefficient P Q h ξ (some (A,B)))
      (idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots B)) f) a=
    idealPatternApplyWithLaws (fun j => markedHarmonicAtom (P j)) (fun j => markedHarmonicAtom (P j))
      (idealResidualCopied (some (A,B))) Θ ζ (idealResidualCoefficient P Q h ξ (some (A,B))) f a := by
  have hBC : idealPatternFreeCoordinates (ell:=ell) (idealResidualFreeSlots B) ⊆
      idealPatternFreeCoordinates (idealResidualFreeSlots (A ∪ B)) :=
    idealPatternFreeCoordinates_mono _ _ (fun j i hi =>
      (mem_idealResidualFreeSlots (A ∪ B) j i).mpr
        (mem_union_right A ((mem_idealResidualFreeSlots B j i).mp hi)))
  rw [idealPatternApply_expectation P hV,idealPatternApply_expectation P hV]
  apply sum_congr rfl
  intro aux _
  change GiantTwoSidedPatternAuxiliary P (idealResidualFreeSlots (A ∪ B)) at aux
  congr 1
  let H := fun b : MarkedPhysicalMarking P (k+ell) =>
    idealResidualCoefficient P Q h ξ (some (A,B)) a b aux*
      ((giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a*
          giantTwoSidedPatternAuxiliaryProduct aux:ℕ):ℂ)^((ζ:ℂ)*Complex.I)*
      idealAdditivePhase Θ (giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a*
        giantTwoSidedPatternAuxiliaryProduct aux)
  have hH : ∀ b c,H (idealMix (idealPatternFreeCoordinates (idealResidualFreeSlots B)) b c)=H b := by
    intro b c
    dsimp only [H]
    exact congrArg (fun z : ℂ => z*
      ((giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a*
        giantTwoSidedPatternAuxiliaryProduct aux:ℕ):ℂ)^((ζ:ℂ)*Complex.I)*
      idealAdditivePhase Θ (giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a*
        giantTwoSidedPatternAuxiliaryProduct aux))
      (idealResidualCoefficient_target_independent P A B hAB Q h ξ a b c aux)
  exact congrFun (idealAverageSet_weighted_subset P hV hP _ _ hBC H f hH) a

end
end ArtinMatthews
