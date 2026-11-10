module

public import ArtinMatthews.IdealPhaseFactor
public import ArtinMatthews.IdealResidualFamily
public import ArtinMatthews.IdealAuxiliarySelected
public import ArtinMatthews.IdealSelectedUnion
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

/-! The actual copied dilation factors into its shared and selected
products, and its full complex phase matches the comparison phase. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealPatternAuxiliaryOfMarking {G : Type*} {P : G → Finset ℕ} {k ell : ℕ}
    (C : G → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell)) :
    GiantTwoSidedPatternAuxiliary P C := fun g i => a g (Fin.castAdd ell i.val)

theorem idealPattern_copied_mul_auxiliary {G : Type*} [Fintype G]
    {P : G → Finset ℕ} {k ell : ℕ} (C : G → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) :
    giantTwoSidedPatternCopiedProduct C a*
      giantTwoSidedPatternAuxiliaryProduct (idealPatternAuxiliaryOfMarking C a)=
      giantTwoSidedPatternCopiedProduct (fun _ => (∅ : Finset (Fin k))) a := by
  unfold giantTwoSidedPatternCopiedProduct giantTwoSidedPatternAuxiliaryProduct idealPatternAuxiliaryOfMarking
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro g _
  rw [prod_coe_sort (C g) (fun i => (a g (Fin.castAdd ell i):ℕ)),prod_sdiff (subset_univ (C g))]
  simp only [sdiff_empty]

theorem idealResidual_copied_product {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (A B : Finset (G × Fin k)) (hAB : Disjoint A B)
    (a : MarkedPhysicalMarking P (k+ell)) :
    giantTwoSidedPatternCopiedProduct (fun _ => (∅ : Finset (Fin k))) a=
      giantTwoSidedPatternCopiedProduct (idealResidualFreeSlots (A ∪ B)) a*
        (idealSelectedProduct (idealResidualSelectedMarking A a)*
          idealSelectedProduct (idealResidualSelectedMarking B a)) := by
  rw [← idealPattern_copied_mul_auxiliary (idealResidualFreeSlots (A ∪ B)) a,
    idealAuxiliarySelected_product]
  have he : idealAuxiliarySelectedEquiv P (A ∪ B)
      (idealPatternAuxiliaryOfMarking (idealResidualFreeSlots (A ∪ B)) a)=
        idealResidualSelectedMarking (A ∪ B) a := rfl
  rw [he,idealSelectedUnion_product P A B hAB]
  rfl

def idealDilationPhase (Θ ζ : ℝ) (D : ℕ) : ℂ :=
  (D:ℂ)^((ζ:ℂ)*Complex.I)*idealAdditivePhase Θ D

theorem idealDilationPhase_selected (Θ ζ : ℝ) (C a b : ℕ) :
    idealDilationPhase Θ ζ (C*(a*b))=
      (C:ℂ)^((ζ:ℂ)*Complex.I)*idealProductPhase ζ (Θ*(C:ℝ)) a b := by
  have hp : ((C*(a*b):ℕ):ℂ)^((ζ:ℂ)*Complex.I)=
      (C:ℂ)^((ζ:ℂ)*Complex.I)*
        (((a:ℝ)*(b:ℝ):ℝ):ℂ)^(Complex.I*(ζ:ℂ)) := by
    rw [Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
    congr 1
    simp only [Complex.ofReal_mul,Complex.ofReal_natCast,Nat.cast_mul]
    rw [mul_comm (ζ:ℂ) Complex.I]
  have hphase : idealAdditivePhase Θ (C*(a*b))=
      (Real.fourierChar ((Θ*(C:ℝ))*(a:ℝ)*(b:ℝ)):ℂ) := by
    unfold idealAdditivePhase
    rw [Real.fourierChar_apply]
    congr 2
    push_cast
    ring
  unfold idealDilationPhase idealProductPhase
  rw [hp,hphase]
  ring

theorem idealDilationPhase_copied_norm {G : Type*} [Fintype G]
    {P : G → Finset ℕ} {k ell : ℕ} (hP : ∀ g p,p∈P g → 0 < p)
    (C : G → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell)) (ζ : ℝ) :
    ‖(giantTwoSidedPatternCopiedProduct C a:ℂ)^((ζ:ℂ)*Complex.I)‖=1 := by
  have hp : 0 < giantTwoSidedPatternCopiedProduct C a :=
    prod_pos fun g _ => prod_pos fun i _ => hP g _ (a g (Fin.castAdd ell i)).property
  rw [Complex.norm_natCast_cpow_of_pos hp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,
    mul_zero,zero_mul,sub_self,Real.rpow_zero]

end
end ArtinMatthews
