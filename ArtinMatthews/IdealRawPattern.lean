module

public import ArtinMatthews.IdealPatternFreeCoordinates
public import ArtinMatthews.IdealPatternExpectation
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

/-! The raw member of the original residual family is exactly the
full first-slot phase followed by tail averaging. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealRawPhase {G : Type*} [Fintype G] {P : G → Finset ℕ} {k ell : ℕ}
    (Θ ζ : ℝ) (a : MarkedPhysicalMarking P (k+ell)) : ℂ :=
  ((giantTwoSidedPatternCopiedProduct (fun _ => (∅ : Finset (Fin k))) a:ℕ):ℂ)^((ζ:ℂ)*Complex.I)*
    idealAdditivePhase Θ (giantTwoSidedPatternCopiedProduct (fun _ => (∅ : Finset (Fin k))) a)

theorem idealRawPhase_norm {G : Type*} [Fintype G] {P : G → Finset ℕ} {k ell : ℕ}
    (hP : ∀ g p,p∈P g → 0 < p) (Θ ζ : ℝ) (a : MarkedPhysicalMarking P (k+ell)) :
    ‖idealRawPhase Θ ζ a‖=1 := by
  have hp : 0 < giantTwoSidedPatternCopiedProduct (fun _ => (∅ : Finset (Fin k))) a :=
    prod_pos fun g _ => prod_pos fun i _ => hP g _ (a g (Fin.castAdd ell i)).property
  unfold idealRawPhase
  rw [norm_mul,idealAdditivePhase_norm,mul_one,Complex.norm_natCast_cpow_of_pos hp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,
    mul_zero,zero_mul,sub_self,Real.rpow_zero]

theorem idealRawPhase_tail_independent {G : Type*} [Fintype G] [DecidableEq G]
    {P : G → Finset ℕ} {k ell : ℕ} (Θ ζ : ℝ) (a b : MarkedPhysicalMarking P (k+ell)) :
    idealRawPhase Θ ζ
      (idealMix (idealPatternFreeCoordinates (fun _ => (∅ : Finset (Fin k)))) a b)=
        idealRawPhase Θ ζ a := by
  have he : giantTwoSidedPatternCopiedProduct (fun _ => (∅ : Finset (Fin k)))
      (idealMix (idealPatternFreeCoordinates (fun _ => (∅ : Finset (Fin k)))) a b)=
        giantTwoSidedPatternCopiedProduct (fun _ => (∅ : Finset (Fin k))) a := by
    apply giantTwoSidedPatternCopiedProduct_eq
    intro g i _
    simp only [idealMix,idealPatternFreeCoordinates_first,notMem_empty,ite_false]
  unfold idealRawPhase
  rw [he]

theorem idealPatternApply_raw {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (Θ ζ : ℝ) (f : MarkedPhysicalMarking P (k+ell) → ℂ) (a : MarkedPhysicalMarking P (k+ell)) :
    idealPatternApplyWithLaws (fun g => markedHarmonicAtom (P g))
      (fun g => markedHarmonicAtom (P g)) (fun _ => (∅ : Finset (Fin k))) Θ ζ (fun _ _ _ => 1) f a=
      idealRawPhase Θ ζ a*
        idealAverageSet P (idealPatternFreeCoordinates (fun _ => (∅ : Finset (Fin k)))) f a := by
  let : Unique (GiantTwoSidedPatternAuxiliary P (fun _ => (∅ : Finset (Fin k)))) := {
    default := fun _ i => (notMem_empty i.val i.property).elim
    uniq := fun aux => by
      funext g i
      exact (notMem_empty i.val i.property).elim }
  rw [idealPatternApply_expectation P hV,Fintype.sum_unique]
  simp only [giantTwoSidedPatternAuxiliaryMass,giantTwoSidedPatternAuxiliaryProduct,
    Fintype.prod_empty,prod_const_one,mul_one,one_mul]
  unfold idealRawPhase idealAverageSet idealLabelExpectation
  simp only [Complex.ofReal_one,one_mul]
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  ring

end
end ArtinMatthews
