module

public import ArtinMatthews.IdealHeadTail
public import ArtinMatthews.IdealPatternFreeCoordinates
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

/-! Every free-pattern average is the corresponding head-coordinate
average of the original tail conditional expectation. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealHeadTest {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (f : MarkedPhysicalMarking P (k+ell) → ℂ)
    (a : MarkedPhysicalMarking P k) : ℂ :=
  idealLabelExpectation P ell (fun b => f (idealLabelAppend a b))

theorem idealHead_expectation {G A : Type*} [Fintype G] [DecidableEq G]
    [CommRing A] [Algebra ℝ A] (P : G → Finset ℕ) {k ell : ℕ}
    (hV : ∀ g,0 < bandReciprocalMass (P g)) (F : MarkedPhysicalMarking P k → A) :
    idealLabelExpectation P (k+ell) (fun a => F (idealLabelHead a))=idealLabelExpectation P k F := by
  rw [idealHeadTail_expectation]
  apply congrArg (idealLabelExpectation P k)
  funext a
  have hh (b : MarkedPhysicalMarking P ell) : idealLabelHead (idealLabelAppend a b)=a := by
    funext g i
    simp [idealLabelHead,idealLabelAppend]
  simp_rw [hh]
  unfold idealLabelExpectation
  rw [← sum_mul,← map_sum,idealLabelMass_sum P ell hV,map_one,one_mul]

theorem idealHeadTest_energy_le {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealLabelEnergy P k (idealHeadTest P f) ≤ idealLabelEnergy P (k+ell) f := by
  have hj (a : MarkedPhysicalMarking P k) : ‖idealHeadTest P f a‖^2 ≤
      ∑ b : MarkedPhysicalMarking P ell,idealLabelMass P ell b*‖f (idealLabelAppend a b)‖^2 :=
    idealWeightedJensen _ (idealLabelMass_nonneg P ell hV) (idealLabelMass_sum P ell hV) _
  calc
    _ ≤ ∑ a : MarkedPhysicalMarking P k,idealLabelMass P k a*
        ∑ b : MarkedPhysicalMarking P ell,idealLabelMass P ell b*‖f (idealLabelAppend a b)‖^2 :=
      sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hj a) (idealLabelMass_nonneg P k hV a)
    _ = _ := (idealHeadTail_expectation P (fun a => ‖f a‖^2)).symm

theorem idealHead_free_average {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (S : Finset (G × Fin k))
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots S)) f a=
      idealAverageSet P S (idealHeadTest P f) (idealLabelHead a) := by
  unfold idealAverageSet
  rw [idealHeadTail_expectation]
  apply congrArg (idealLabelExpectation P k)
  funext b
  unfold idealHeadTest
  apply congrArg (idealLabelExpectation P ell)
  funext c
  congr 1
  funext g i
  induction i using Fin.addCases with
  | left i =>
    simp only [idealMix,idealPatternFreeCoordinates_first,mem_idealResidualFreeSlots,
      idealLabelHead,idealLabelAppend,Fin.addCases_left]
    split_ifs <;> rfl
  | right i =>
    simp only [idealMix,idealPatternFreeCoordinates_tail,ite_true,
      idealLabelAppend,Fin.addCases_right]

end
end ArtinMatthews
