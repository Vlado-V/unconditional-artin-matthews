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

/-! Nonzero terms of the primewise expansion are genuine compatible
lifespans: active lines coincide, chosen ghosts have the right order and
line, and an orphan has two distinct ordered endpoints. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ} {L : Type*} [DecidableEq L]
  (eta : Fin (N+1) → ℝ) (line : Fin (N+1) → L)

theorem markedMemoryPrefixChoice_nonzero (a h : Fin (N+1))
    (hn : markedMemoryPrefixChoice eta line a (some h)≠0) : h<a ∧ line h=line a := by
  have hlt : h<a := by
    by_contra hlt
    simp only [markedMemoryPrefixChoice,ite_eq_right hlt] at hn
    exact hn rfl
  have he : line a=line h := by
    by_contra he
    simp only [markedMemoryPrefixChoice,ite_eq_left hlt,markedLineHit,ite_eq_right he,
      mul_zero,zero_mul] at hn
    exact hn rfl
  exact ⟨hlt,he.symm⟩

theorem markedMemorySuffixChoice_nonzero (a c h : Fin (N+1))
    (hn : markedMemorySuffixChoice eta line a c (some h)≠0) : c<h ∧ line h=line a := by
  have hlt : c<h := by
    by_contra hlt
    simp only [markedMemorySuffixChoice,ite_eq_right hlt] at hn
    exact hn rfl
  have he : line a=line h := by
    by_contra he
    simp only [markedMemorySuffixChoice,ite_eq_left hlt,markedLineHit,ite_eq_right he,
      mul_zero,zero_mul] at hn
    exact hn rfl
  exact ⟨hlt,he.symm⟩

def MarkedMemoryPrimeLifespanCompatible (A : Finset (Fin (N+1)))
    (c : MarkedMemoryPrimeLifespanChoice N) : Prop :=
  if hA : A.Nonempty then
    MarkedMemoryActiveCoherent A line (A.min' hA) ∧
      (∀ h,c.1=some h → h<A.min' hA ∧ line h=line (A.min' hA)) ∧
      (∀ h,c.2=some h → A.max' hA<h ∧ line h=line (A.min' hA))
  else c=(none,none) ∨ ∃ a b,c=(some a,some b) ∧ a<b ∧ line a=line b

theorem markedMemoryPrimeLifespanChoice_nonzero (A : Finset (Fin (N+1))) (atom : ℝ)
    (c : MarkedMemoryPrimeLifespanChoice N)
    (hn : markedMemoryPrimeLifespanChoiceWeight eta line A atom c≠0) :
    MarkedMemoryPrimeLifespanCompatible line A c := by
  by_cases hA : A.Nonempty
  · rw [markedMemoryPrimeLifespanChoiceWeight,dite_eq_left hA] at hn
    have hc : MarkedMemoryActiveCoherent A line (A.min' hA) := by
      by_contra hc
      rw [ite_eq_right hc,mul_zero] at hn
      exact hn rfl
    rw [ite_eq_left hc] at hn
    have hprod := (mul_ne_zero_iff.mp hn).2
    have hp := (mul_ne_zero_iff.mp ((mul_ne_zero_iff.mp hprod).1)).1
    have hs := (mul_ne_zero_iff.mp hprod).2
    rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_left hA]
    refine ⟨hc,?_,?_⟩
    · intro h hh
      rw [hh] at hp
      exact markedMemoryPrefixChoice_nonzero eta line _ h hp
    · intro h hh
      rw [hh] at hs
      exact markedMemorySuffixChoice_nonzero eta line _ _ h hs
  · rw [markedMemoryPrimeLifespanChoiceWeight,dite_eq_right hA] at hn
    rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_right hA]
    rcases c with ⟨a,b⟩
    cases a with
    | none =>
      cases b with
      | none => exact Or.inl rfl
      | some b => exact False.elim (hn rfl)
    | some a =>
      cases b with
      | none => exact False.elim (hn rfl)
      | some b =>
        have hab : a<b := by
          by_contra hab
          simp only [markedMemoryOrphanChoice,ite_eq_right hab] at hn
          exact hn rfl
        have he : line a=line b := by
          by_contra he
          simp only [markedMemoryOrphanChoice,ite_eq_left hab,ite_eq_right he,mul_zero] at hn
          exact hn rfl
        exact Or.inr ⟨a,b,rfl,hab,he⟩

end
end ArtinMatthews
