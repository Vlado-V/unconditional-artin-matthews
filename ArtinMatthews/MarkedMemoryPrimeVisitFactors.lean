module

public import ArtinMatthews.MarkedMemoryPrimeLifespanChoices
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Literal per-visit factors for optional first/last ghosts. Their finite
products are exactly the signed prefix, internal and suffix terms in
the independent-line expansion. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ} {L : Type*} (eta : Fin (N+1) → ℝ) (line : Fin (N+1) → L)

abbrev markedMemoryPrimeDamping (a v : Fin (N+1)) : ℝ :=
  1-eta v*markedLineHit line v (line a)

def markedMemoryPrefixVisitFactor (a : Fin (N+1)) (o : Option (Fin (N+1))) (v : Fin (N+1)) : ℝ :=
  match o with
  | none => 1
  | some h => (if v=h then -eta h*markedLineHit line h (line a) else 1)*
      (if h<v ∧ v<a then markedMemoryPrimeDamping eta line a v else 1)

def markedMemorySuffixVisitFactor (a b : Fin (N+1)) (o : Option (Fin (N+1))) (v : Fin (N+1)) : ℝ :=
  match o with
  | none => 1
  | some h => (if v=h then -eta h*markedLineHit line h (line a) else 1)*
      (if b<v ∧ v<h then markedMemoryPrimeDamping eta line a v else 1)

def markedMemoryInternalVisitFactor (A : Finset (Fin (N+1))) (a b v : Fin (N+1)) : ℝ :=
  if a<v ∧ v<b ∧ v∉A then markedMemoryPrimeDamping eta line a v else 1

theorem markedMemoryPrefixVisitFactor_prod (a : Fin (N+1)) (o : Option (Fin (N+1)))
    (ho : ∀ h,o=some h → h<a) :
    (∏ v,markedMemoryPrefixVisitFactor eta line a o v)=markedMemoryPrefixChoice eta line a o := by
  cases o with
  | none => simp [markedMemoryPrefixVisitFactor,markedMemoryPrefixChoice]
  | some h =>
    simp only [markedMemoryPrefixVisitFactor]
    rw [Finset.prod_mul_distrib]
    simp [markedMemoryPrefixChoice,ho h rfl,Finset.prod_filter,markedMemoryPrimeDamping]

theorem markedMemorySuffixVisitFactor_prod (a b : Fin (N+1)) (o : Option (Fin (N+1)))
    (ho : ∀ h,o=some h → b<h) :
    (∏ v,markedMemorySuffixVisitFactor eta line a b o v)=markedMemorySuffixChoice eta line a b o := by
  cases o with
  | none => simp [markedMemorySuffixVisitFactor,markedMemorySuffixChoice]
  | some h =>
    simp only [markedMemorySuffixVisitFactor]
    rw [Finset.prod_mul_distrib]
    simp [markedMemorySuffixChoice,ho h rfl,Finset.prod_filter,markedMemoryPrimeDamping]

theorem markedMemoryInternalVisitFactor_prod (A : Finset (Fin (N+1))) (a b : Fin (N+1)) :
    (∏ v,markedMemoryInternalVisitFactor eta line A a b v)=markedMemoryInternalDamping A eta line a b := by
  simp only [markedMemoryInternalVisitFactor,markedMemoryInternalDamping,markedMemoryInternal,
    Finset.prod_filter]

end
end ArtinMatthews
