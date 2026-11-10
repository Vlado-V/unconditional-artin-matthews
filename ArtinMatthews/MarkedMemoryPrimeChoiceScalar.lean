module

public import ArtinMatthews.MarkedMemoryPrimeIntervalScalar
public import ArtinMatthews.MarkedMemoryPrimeOrphanScalar
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Elementwise scalar preservation between the exact one-prime line
choice and its literal half-step lifespan endpoint factors. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ} {L : Type*} (eta : Fin (N+1) → ℝ) (line : Fin (N+1) → L)

theorem markedMemoryPrimeIntervalScalar_active (A : Finset (Fin (N+1)))
    (c : MarkedMemoryPrimeLifespanChoice N) (hA : A.Nonempty)
    (hc : MarkedMemoryPrimeLifespanCompatible line A c) :
    markedMemoryPrimeIntervalScalar eta line A c=
      markedMemoryPrefixChoice eta line (A.min' hA) c.1*
        markedMemoryInternalDamping A eta line (A.min' hA) (A.max' hA)*
          markedMemorySuffixChoice eta line (A.min' hA) (A.max' hA) c.2 := by
  have hc' := hc
  rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_left hA] at hc'
  unfold markedMemoryPrimeIntervalScalar
  simp_rw [markedMemoryPrimeIntervalVisitScalar_active eta line A c hA hc]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  rw [markedMemoryPrefixVisitFactor_prod eta line _ _ (fun h hh => (hc'.2.1 h hh).1),
    markedMemoryInternalVisitFactor_prod,
    markedMemorySuffixVisitFactor_prod eta line _ _ _ (fun h hh => (hc'.2.2 h hh).1)]

theorem markedMemoryPrimeChoiceWeight_interval (A : Finset (Fin (N+1)))
    (atom : ℝ) (c : MarkedMemoryPrimeLifespanChoice N)
    (hc : MarkedMemoryPrimeLifespanCompatible line A c) :
    markedMemoryPrimeLifespanChoiceWeight eta line A atom c=
      if MarkedMemoryPrimeLifespanUsed A c then atom*markedMemoryPrimeIntervalScalar eta line A c else 1 := by
  by_cases hA : A.Nonempty
  · have hu : MarkedMemoryPrimeLifespanUsed A c := Or.inl hA
    have hc' := hc
    rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_left hA] at hc'
    rw [ite_eq_left hu,markedMemoryPrimeLifespanChoiceWeight,dite_eq_left hA,ite_eq_left hc'.1,
      markedMemoryPrimeIntervalScalar_active eta line A c hA hc]
  · have hE : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_right Finset.not_nonempty_empty] at hc
    rcases hc with rfl | ⟨a,b,rfl,hab,he⟩
    · simp [markedMemoryPrimeLifespanChoiceWeight,markedMemoryOrphanChoice,MarkedMemoryPrimeLifespanUsed]
    · have hu : MarkedMemoryPrimeLifespanUsed (∅ : Finset (Fin (N+1))) (some a,some b) := by
        apply Or.inr
        simp
      rw [ite_eq_left hu,markedMemoryPrimeLifespanChoiceWeight,dite_eq_right Finset.not_nonempty_empty,
        markedMemoryOrphanChoice,ite_eq_left hab,ite_eq_left he,
        markedMemoryPrimeIntervalScalar_orphan eta line a b hab he]

theorem markedMemoryPrimeChoiceWeight_used_interval (A : Finset (Fin (N+1)))
    (atom : ℝ) (c : MarkedMemoryPrimeLifespanChoice N)
    (hc : MarkedMemoryPrimeLifespanCompatible line A c) (hu : MarkedMemoryPrimeLifespanUsed A c) :
    markedMemoryPrimeLifespanChoiceWeight eta line A atom c=atom*markedMemoryPrimeIntervalScalar eta line A c := by
  rw [markedMemoryPrimeChoiceWeight_interval eta line A atom c hc,ite_eq_left hu]

end
end ArtinMatthews
