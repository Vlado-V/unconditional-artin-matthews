module

public import ArtinMatthews.IdealSelectedComparisonTransport
public import ArtinMatthews.IdealSelectedFill
public import ArtinMatthews.IdealSelectedUnion
public import ArtinMatthews.IdealHeadProducts
public import ArtinMatthews.IdealPatternProducts
public import ArtinMatthews.IdealSelectedConditionalBound
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

/-! The shared first-slot product changes the comparison frequency
without changing its norm or any harmonic measure. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealResidualHeadKernel {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k : ℕ} (A B : Finset (G × Fin k))
    (Q : ℕ) (h ξ Θ ζ : ℝ) (a : MarkedPhysicalMarking P k)
    (x : IdealSelectedLabels (idealResidualBands P A))
    (y : IdealSelectedLabels (idealResidualBands P B)) : ℂ :=
  (giantTwoSidedPatternCopiedProduct (ell:=0) (idealResidualFreeSlots (A ∪ B)) a:ℂ)^((ζ:ℂ)*Complex.I)*
    (idealProductPhase ζ (Θ*(giantTwoSidedPatternCopiedProduct (ell:=0) (idealResidualFreeSlots (A ∪ B)) a:ℝ))
      (idealSelectedProduct x) (idealSelectedProduct y)-
    idealFullCellPhaseAverage (idealResidualBands P A) (idealResidualBands P B) Q h ξ ζ
      (Θ*(giantTwoSidedPatternCopiedProduct (ell:=0) (idealResidualFreeSlots (A ∪ B)) a:ℝ)) x y)

theorem idealResidualHeadKernel_invariant {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k : ℕ} (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (Q : ℕ) (h ξ Θ ζ : ℝ) (a : MarkedPhysicalMarking P k)
    (x : IdealSelectedLabels (idealResidualBands P A))
    (y : IdealSelectedLabels (idealResidualBands P B)) :
    idealResidualHeadKernel P A B Q h ξ Θ ζ
      (idealSelectedFill (A ∪ B) a ((idealSelectedUnionEquiv P A B hAB).symm (x,y))) x y=
      idealResidualHeadKernel P A B Q h ξ Θ ζ a x y := by
  unfold idealResidualHeadKernel
  rw [idealCopiedProduct_fill]

theorem idealResidualHeadKernel_slice_bound {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k : ℕ} (hP : ∀ j p,p∈P j → 0 < p)
    (A B : Finset (G × Fin k)) (Q : ℕ) (h ξ Θ ζ ε : ℝ)
    (hcmp : ∀ α f g,‖idealSelectedComparisonForm (idealResidualBands P A) (idealResidualBands P B)
      Q h ξ ζ α f g‖ ≤ ε*Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P A)) f)*
        Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P B)) g))
    (a : MarkedPhysicalMarking P k)
    (f : IdealSelectedLabels (idealResidualBands P A) → ℂ)
    (g : IdealSelectedLabels (idealResidualBands P B) → ℂ) :
    ‖∑ x,(idealSelectedMass (idealResidualBands P A) x:ℂ)*f x*
      ∑ y,(idealSelectedMass (idealResidualBands P B) y:ℂ)*g y*
        idealResidualHeadKernel P A B Q h ξ Θ ζ a x y‖ ≤
      ε*Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P A)) f)*
        Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P B)) g) := by
  have he : (∑ x,(idealSelectedMass (idealResidualBands P A) x:ℂ)*f x*
      ∑ y,(idealSelectedMass (idealResidualBands P B) y:ℂ)*g y*
        idealResidualHeadKernel P A B Q h ξ Θ ζ a x y)=
      (giantTwoSidedPatternCopiedProduct (ell:=0) (idealResidualFreeSlots (A ∪ B)) a:ℂ)^((ζ:ℂ)*Complex.I)*
        idealSelectedComparisonForm (idealResidualBands P A) (idealResidualBands P B) Q h ξ ζ
          (Θ*(giantTwoSidedPatternCopiedProduct (ell:=0) (idealResidualFreeSlots (A ∪ B)) a:ℝ)) f g := by
    unfold idealResidualHeadKernel idealSelectedComparisonForm
    simp only [mul_sum]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y _
    ring
  rw [he,norm_mul,idealDilationPhase_copied_norm hP,one_mul]
  exact hcmp _ f g

theorem idealResidualHeadKernel_bound {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hP : ∀ j p,p∈P j → 0 < p) (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (Q : ℕ) (h ξ Θ ζ : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hcmp : ∀ α f g,‖idealSelectedComparisonForm (idealResidualBands P A) (idealResidualBands P B)
      Q h ξ ζ α f g‖ ≤ ε*Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P A)) f)*
        Real.sqrt (idealFrameEnergy (idealSelectedMass (idealResidualBands P B)) g))
    (f g : MarkedPhysicalMarking P k → ℂ)
    (hf : ∀ a b,f (idealMix A a b)=f a) (hg : ∀ a b,g (idealMix B a b)=g a) :
    ‖idealLabelExpectation P k (fun a => star (f a)*g a*
      idealResidualHeadKernel P A B Q h ξ Θ ζ a (idealFullSelectedLabels A a) (idealFullSelectedLabels B a))‖ ≤
      ε*Real.sqrt (idealLabelEnergy P k f)*Real.sqrt (idealLabelEnergy P k g) :=
  idealSelectedConditional_pairing_bound P hV A B hAB
    (idealResidualHeadKernel P A B Q h ξ Θ ζ)
    (idealResidualHeadKernel_invariant P A B hAB Q h ξ Θ ζ) hε
    (idealResidualHeadKernel_slice_bound P hP A B Q h ξ Θ ζ ε hcmp) f g hf hg

end
end ArtinMatthews
