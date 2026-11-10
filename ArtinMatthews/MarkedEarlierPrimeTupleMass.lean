module

public import ArtinMatthews.MarkedEarlierPrimePrescribed
public import Mathlib.Data.Fintype.Pi
public import ArtinMatthews.MarkedTriangularPrimeMass
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite product-mass bounds for equality prescriptions that may
depend on earlier prime draws. A selected coordinate costs one atom bound;
an unselected coordinate costs its full band mass. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedEarlierPrimeTuple_sum_eq_zero {n : ℕ} {P : Fin n → Finset Nat.Primes}
    (ν : (i : Fin n) → ↥(P i) → ℝ) (S : Finset (Fin n))
    (target : (i : Fin n) → (Fin i.val → Nat.Primes) → Option Nat.Primes)
    (i : Fin n) (hi : i∈S)
    (hbad : ∀ prior p,some (p : P i).1≠target i prior) :
    (∑ t : (i : Fin n) → ↥(P i),
      if MarkedEarlierPrimeTuplePrescribed S target t then ∏ i,ν i (t i) else 0)=0 := by
  apply Finset.sum_eq_zero
  intro t _
  apply ite_eq_right
  intro ht
  exact hbad (markedPrimeTuplePrefix t i) (t i) (ht i hi)

theorem markedEarlierPrimeTuple_sum_eq_zero_of_none {n : ℕ} {P : Fin n → Finset Nat.Primes}
    (ν : (i : Fin n) → ↥(P i) → ℝ) (S : Finset (Fin n))
    (target : (i : Fin n) → (Fin i.val → Nat.Primes) → Option Nat.Primes)
    (i : Fin n) (hi : i∈S) (hnone : ∀ prior,target i prior=none) :
    (∑ t : (i : Fin n) → ↥(P i),
      if MarkedEarlierPrimeTuplePrescribed S target t then ∏ i,ν i (t i) else 0)=0 := by
  apply markedEarlierPrimeTuple_sum_eq_zero ν S target i hi
  intro prior p
  rw [hnone prior]
  exact Option.some_ne_none _

theorem markedEarlierPrimeTuple_sum_eq_zero_of_outside {n : ℕ} {P : Fin n → Finset Nat.Primes}
    (ν : (i : Fin n) → ↥(P i) → ℝ) (S : Finset (Fin n))
    (target : (i : Fin n) → (Fin i.val → Nat.Primes) → Option Nat.Primes)
    (i : Fin n) (hi : i∈S)
    (hout : ∀ prior q,target i prior=some q → q∉P i) :
    (∑ t : (i : Fin n) → ↥(P i),
      if MarkedEarlierPrimeTuplePrescribed S target t then ∏ i,ν i (t i) else 0)=0 := by
  apply markedEarlierPrimeTuple_sum_eq_zero ν S target i hi
  intro prior p hp
  exact hout prior p.1 hp.symm p.2

theorem markedEarlierPrimeCost_product {n : ℕ} (S : Finset (Fin n)) (Δ N : ℝ) :
    (∏ i : Fin n,if i∈S then Δ else N)=Δ^S.card*N^(n-S.card) := by
  rw [Finset.prod_ite]
  have hs : (Finset.univ.filter (fun i : Fin n => i∈S))=S := by ext i; simp
  have hn : (Finset.univ.filter (fun i : Fin n => i∉S))=Finset.univ\S := by ext i; simp
  rw [hs,hn,Finset.prod_const,Finset.prod_const,
    Finset.card_sdiff_of_subset (Finset.subset_univ S),Finset.card_univ,Fintype.card_fin]

theorem markedEarlierPrimeTuple_sum_le_product {n : ℕ} {P : Fin n → Finset Nat.Primes}
    (ν : (i : Fin n) → ↥(P i) → ℝ) (hν : ∀ i p,0 ≤ ν i p)
    {Δ N : ℝ} (hΔ : 0 ≤ Δ) (hN : 0 ≤ N)
    (hatom : ∀ i p,ν i p ≤ Δ) (hmass : ∀ i,(∑ p : P i,ν i p) ≤ N)
    (S : Finset (Fin n))
    (target : (i : Fin n) → (Fin i.val → Nat.Primes) → Option Nat.Primes) :
    (∑ t : (i : Fin n) → ↥(P i),
      if MarkedEarlierPrimeTuplePrescribed S target t then ∏ i,ν i (t i) else 0) ≤
      ∏ i : Fin n,if i∈S then Δ else N := by
  have h := markedTriangularPrimeMass_le n P (markedEarlierPrimeKernel ν S target)
    (fun i => if i∈S then Δ else N)
    (markedEarlierPrimeKernel_nonneg ν hν S target)
    (fun i => by split_ifs <;> assumption)
    (markedEarlierPrimeKernel_row_le ν hΔ hatom hmass S target)
  simpa only [markedTriangularPrimeWeight,markedEarlierPrimeKernel_product] using h

theorem markedEarlierPrimeTuple_sum_le {n : ℕ} {P : Fin n → Finset Nat.Primes}
    (ν : (i : Fin n) → ↥(P i) → ℝ) (hν : ∀ i p,0 ≤ ν i p)
    {Δ N : ℝ} (hΔ : 0 ≤ Δ) (hN : 0 ≤ N)
    (hatom : ∀ i p,ν i p ≤ Δ) (hmass : ∀ i,(∑ p : P i,ν i p) ≤ N)
    (S : Finset (Fin n))
    (target : (i : Fin n) → (Fin i.val → Nat.Primes) → Option Nat.Primes) :
    (∑ t : (i : Fin n) → ↥(P i),
      if MarkedEarlierPrimeTuplePrescribed S target t then ∏ i,ν i (t i) else 0) ≤
      Δ^S.card*N^(n-S.card) := by
  simpa only [markedEarlierPrimeCost_product] using
    markedEarlierPrimeTuple_sum_le_product ν hν hΔ hN hatom hmass S target

theorem markedEarlierPrimeTuple_sum_le_slack {n : ℕ} {P : Fin n → Finset Nat.Primes}
    (ν : (i : Fin n) → ↥(P i) → ℝ) (hν : ∀ i p,0 ≤ ν i p)
    {Δ N : ℝ} (hΔ : 0 ≤ Δ) (hN : 1 ≤ N)
    (hatom : ∀ i p,ν i p ≤ Δ) (hmass : ∀ i,(∑ p : P i,ν i p) ≤ N)
    (S : Finset (Fin n))
    (target : (i : Fin n) → (Fin i.val → Nat.Primes) → Option Nat.Primes) :
    (∑ t : (i : Fin n) → ↥(P i),
      if MarkedEarlierPrimeTuplePrescribed S target t then ∏ i,ν i (t i) else 0) ≤
      Δ^S.card*N^n := by
  refine (markedEarlierPrimeTuple_sum_le ν hν hΔ (zero_le_one.trans hN) hatom hmass S target).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN (Nat.sub_le n S.card))
    (pow_nonneg hΔ _)

def markedEarlierPrimeParentTarget {n : ℕ}
    (parent : (i : Fin n) → Option (Fin i.val)) (old : Fin n → Option Nat.Primes)
    (i : Fin n) (prior : Fin i.val → Nat.Primes) : Option Nat.Primes :=
  match parent i with
  | some j => some (prior j)
  | none => old i

theorem markedEarlierPrimeParentTarget_some {n : ℕ}
    (parent : (i : Fin n) → Option (Fin i.val)) (old : Fin n → Option Nat.Primes)
    (i : Fin n) (j : Fin i.val) (hj : parent i=some j)
    (prior : Fin i.val → Nat.Primes) :
    markedEarlierPrimeParentTarget parent old i prior=some (prior j) := by
  simp only [markedEarlierPrimeParentTarget,hj]

theorem markedEarlierPrimeParentTarget_none {n : ℕ}
    (parent : (i : Fin n) → Option (Fin i.val)) (old : Fin n → Option Nat.Primes)
    (i : Fin n) (hi : parent i=none) (prior : Fin i.val → Nat.Primes) :
    markedEarlierPrimeParentTarget parent old i prior=old i := by
  simp only [markedEarlierPrimeParentTarget,hi]

theorem markedEarlierPrimeParentTuple_sum_le {n : ℕ} {P : Fin n → Finset Nat.Primes}
    (ν : (i : Fin n) → ↥(P i) → ℝ) (hν : ∀ i p,0 ≤ ν i p)
    {Δ N : ℝ} (hΔ : 0 ≤ Δ) (hN : 0 ≤ N)
    (hatom : ∀ i p,ν i p ≤ Δ) (hmass : ∀ i,(∑ p : P i,ν i p) ≤ N)
    (S : Finset (Fin n)) (parent : (i : Fin n) → Option (Fin i.val))
    (old : Fin n → Option Nat.Primes) :
    (∑ t : (i : Fin n) → ↥(P i),
      if MarkedEarlierPrimeTuplePrescribed S (markedEarlierPrimeParentTarget parent old) t
      then ∏ i,ν i (t i) else 0) ≤ Δ^S.card*N^(n-S.card) :=
  markedEarlierPrimeTuple_sum_le ν hν hΔ hN hatom hmass S _

end
end ArtinMatthews
