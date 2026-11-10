module

public import ArtinMatthews.MarkedMemoryTiltPrimewiseActual
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A finite, literal one-lifespan choice at each prime. A nonempty
active set has optional prefix/suffix ghosts. An empty active set has
either no lifespan or a strict two-ended orphan; singleton ghosts have
weight zero and are already included in the extracted baseline. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev MarkedMemoryPrimeLifespanChoice (N : ℕ) :=
  Option (Fin (N+1)) × Option (Fin (N+1))

variable {N : ℕ} {L : Type*} [DecidableEq L]
  (eta : Fin (N+1) → ℝ) (line : Fin (N+1) → L)

def markedMemoryPrefixChoice (a : Fin (N+1)) : Option (Fin (N+1)) → ℝ
  | none => 1
  | some h => if h<a then -eta h*markedLineHit line h (line a)*
      ∏ j ∈ Finset.univ.filter (fun j => h<j ∧ j<a),
        (1-eta j*markedLineHit line j (line a)) else 0

def markedMemorySuffixChoice (a c : Fin (N+1)) : Option (Fin (N+1)) → ℝ
  | none => 1
  | some h => if c<h then -eta h*markedLineHit line h (line a)*
      ∏ j ∈ Finset.univ.filter (fun j => c<j ∧ j<h),
        (1-eta j*markedLineHit line j (line a)) else 0

theorem markedMemoryPrefixChoice_sum (a : Fin (N+1)) :
    (∑ h : Option (Fin (N+1)),markedMemoryPrefixChoice eta line a h)=
      markedMemoryPrefixGhost eta line a := by
  have hs : (∑ h : Fin (N+1),markedMemoryPrefixChoice eta line a (some h)) =
      -(∑ h ∈ markedMemoryBefore N a,eta h*markedLineHit line h (line a)*
        ∏ j ∈ Finset.univ.filter (fun j => h<j ∧ j<a),
          (1-eta j*markedLineHit line j (line a))) := by
    rw [markedMemoryBefore,Finset.sum_filter,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : h<a
    · simp only [markedMemoryPrefixChoice,hh,ite_true]
      ring
    · simp only [markedMemoryPrefixChoice,hh,ite_false,neg_zero]
  rw [Fintype.sum_option,hs]
  simp only [markedMemoryPrefixChoice,markedMemoryPrefixGhost,sub_eq_add_neg]

theorem markedMemorySuffixChoice_sum (a c : Fin (N+1)) :
    (∑ h : Option (Fin (N+1)),markedMemorySuffixChoice eta line a c h)=
      markedMemorySuffixGhost eta line a c := by
  have hs : (∑ h : Fin (N+1),markedMemorySuffixChoice eta line a c (some h)) =
      -(∑ h ∈ markedMemoryAfter N c,eta h*markedLineHit line h (line a)*
        ∏ j ∈ Finset.univ.filter (fun j => c<j ∧ j<h),
          (1-eta j*markedLineHit line j (line a))) := by
    rw [markedMemoryAfter,Finset.sum_filter,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : c<h
    · simp only [markedMemorySuffixChoice,hh,ite_true]
      ring
    · simp only [markedMemorySuffixChoice,hh,ite_false,neg_zero]
  rw [Fintype.sum_option,hs]
  simp only [markedMemorySuffixChoice,markedMemorySuffixGhost,sub_eq_add_neg]

def markedMemoryOrphanChoice (atom : ℝ) : MarkedMemoryPrimeLifespanChoice N → ℝ
  | (none,none) => 1
  | (some a,some c) => if a<c then atom *
      (if line a=line c then eta a*eta c*
        ∏ j ∈ Finset.univ.filter (fun j => a<j ∧ j<c),
          (1-eta j*markedLineHit line j (line a)) else 0) else 0
  | _ => 0

theorem markedMemoryOrphanChoice_sum (atom : ℝ) :
    (∑ c : MarkedMemoryPrimeLifespanChoice N,markedMemoryOrphanChoice eta line atom c)=
      1+atom*markedMemoryOrphanGhostSum eta line := by
  simp only [Fintype.sum_prod_type,Fintype.sum_option,markedMemoryOrphanChoice,
    Finset.sum_const_zero,zero_add,add_zero]
  unfold markedMemoryOrphanGhostSum
  simp only [Finset.sum_filter,Finset.mul_sum,mul_ite,mul_zero]

def markedMemoryPrimeLifespanChoiceWeight (A : Finset (Fin (N+1))) (atom : ℝ)
    (c : MarkedMemoryPrimeLifespanChoice N) : ℝ :=
  if hA : A.Nonempty then atom *
    (if MarkedMemoryActiveCoherent A line (A.min' hA) then
      markedMemoryPrefixChoice eta line (A.min' hA) c.1 *
        markedMemoryInternalDamping A eta line (A.min' hA) (A.max' hA) *
        markedMemorySuffixChoice eta line (A.min' hA) (A.max' hA) c.2 else 0)
  else markedMemoryOrphanChoice eta line atom c

theorem markedMemoryPrimeLifespanChoiceWeight_active_sum (A : Finset (Fin (N+1)))
    (hA : A.Nonempty) (atom : ℝ) :
    (∑ c : MarkedMemoryPrimeLifespanChoice N,markedMemoryPrimeLifespanChoiceWeight eta line A atom c)=
      atom*(if MarkedMemoryActiveCoherent A line (A.min' hA) then
        markedMemoryPrefixGhost eta line (A.min' hA) *
          markedMemoryInternalDamping A eta line (A.min' hA) (A.max' hA) *
          markedMemorySuffixGhost eta line (A.min' hA) (A.max' hA) else 0) := by
  have hp := markedMemoryPrefixChoice_sum eta line (A.min' hA)
  have hs := markedMemorySuffixChoice_sum eta line (A.min' hA) (A.max' hA)
  rw [← hp,← hs]
  by_cases hc : MarkedMemoryActiveCoherent A line (A.min' hA)
  · simp only [markedMemoryPrimeLifespanChoiceWeight,dite_eq_left hA,ite_eq_left hc,Fintype.sum_prod_type,
      Finset.mul_sum,Finset.sum_mul,mul_assoc]
    exact Finset.sum_comm
  · simp only [markedMemoryPrimeLifespanChoiceWeight,dite_eq_left hA,ite_eq_right hc,mul_zero,
      Finset.sum_const_zero]

theorem markedMemoryPrimeLifespanChoiceWeight_empty_sum (atom : ℝ) :
    (∑ c : MarkedMemoryPrimeLifespanChoice N,markedMemoryPrimeLifespanChoiceWeight eta line ∅ atom c)=
      1+atom*markedMemoryOrphanGhostSum eta line := by
  simp only [markedMemoryPrimeLifespanChoiceWeight,Finset.not_nonempty_empty,dite_false]
  exact markedMemoryOrphanChoice_sum eta line atom

end
end ArtinMatthews
