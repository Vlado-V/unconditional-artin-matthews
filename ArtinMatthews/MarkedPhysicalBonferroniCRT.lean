module

public import ArtinMatthews.MarkedPhysicalBonferroniResidue
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Exact finite CRT averaging of the selected physical damping monomial.
The independent projective lines and their 1/(p+1) normalization follow
from the already proved finite SL2 action, rather than an assumption. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalLineTupleHit {S : ℕ} (ell : MarkedRootLineTuple S)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (p : ℕ) : Prop :=
  if hp : p ∈ S.primeFactors then
    let _ : Fact p.Prime := ⟨(Nat.mem_primeFactors.mp hp).1⟩
    markedPrimePositionLine p z hz = ell ⟨p,hp⟩
  else False

def markedPhysicalLineVisitFactor {S : ℕ} (ell : MarkedRootLineTuple S)
    (active : Finset ℕ) (r : ℝ) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (p : ℕ) : ℝ :=
  if p ∈ active then 1 else if markedPhysicalLineTupleHit ell z hz p then r else 1

def markedPhysicalLinePrimePathFactor {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M S : ℕ}
    (ell : MarkedRootLineTuple S) (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (p : ℕ) : ℝ :=
  ∏ v ∈ I,markedPhysicalLineVisitFactor ell (markedPhysicalActivePrimes (a v)) (r v) (z v) (hz v) p

def markedPhysicalLinePrimeLoss {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M S : ℕ}
    (ell : MarkedRootLineTuple S) (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (p : ℕ) : ℝ :=
  1-markedPhysicalLinePrimePathFactor ell I a r z hz p

def markedPhysicalLineBonferroniMonomial {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M S : ℕ}
    (ell : MarkedRootLineTuple S) (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ) : ℝ :=
  (∏ p ∈ markedPhysicalPathUsedPrimes I a,markedPhysicalLinePrimePathFactor ell I a r z hz p)*
    ∏ p ∈ T,markedPhysicalLinePrimeLoss ell I a r z hz p

theorem markedPhysicalResidueBonferroniMonomial_eq_lines
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M S : ℕ}
    (hS : Squarefree S) (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ) :
    markedPhysicalResidueBonferroniMonomial hS g I a r z hz T =
      markedPhysicalLineBonferroniMonomial (markedRootKernelTuple hS g) I a r z hz T := rfl

theorem marked_squarefree_root_kernel_tuple_average_real {S : ℕ} [NeZero S]
    (hS : Squarefree S) (f : MarkedRootLineTuple S → ℝ) :
    (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),f (markedRootKernelTuple hS g))/
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ) =
      (∑ ell : MarkedRootLineTuple S,f ell)/((∏ p : S.primeFactors,((p:ℕ)+1):ℕ):ℝ) := by
  have hh := marked_squarefree_root_kernel_tuple_average hS (fun ell => (f ell:ℂ))
  apply Complex.ofReal_injective
  push_cast
  simpa only [div_eq_mul_inv,mul_comm,Nat.cast_prod,Nat.cast_add,Nat.cast_one] using hh

theorem markedPhysicalResidueBonferroniMonomial_average
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M S : ℕ} [NeZero S]
    (hS : Squarefree S) (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ) :
    (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),markedPhysicalResidueBonferroniMonomial hS g I a r z hz T)/
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ) =
      (∑ ell : MarkedRootLineTuple S,markedPhysicalLineBonferroniMonomial ell I a r z hz T)/
        ((∏ p : S.primeFactors,((p:ℕ)+1):ℕ):ℝ) :=
  marked_squarefree_root_kernel_tuple_average_real hS (fun ell => markedPhysicalLineBonferroniMonomial ell I a r z hz T)

end ArtinMatthews
