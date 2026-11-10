module

public import ArtinMatthews.MarkedEarlierPrimePrescribed
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Card
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

/-! A genuine increasing enumeration transports earlier prime values
and the selected-coordinate set without changing the literal tuple law. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {A : Type*} [LinearOrder A]

def markedOrderedPrimeTuplePrefix {P : A → Finset Nat.Primes}
    (t : (a : A) → ↥(P a)) (a : A) : {b : A // b<a} → Nat.Primes :=
  fun b => (t b.1).1

def MarkedOrderedPrimeTuplePrescribed {P : A → Finset Nat.Primes}
    (S : Finset A) (target : (a : A) → ({b : A // b<a} → Nat.Primes) → Option Nat.Primes)
    (t : (a : A) → ↥(P a)) : Prop :=
  ∀ a∈S,some (t a).1=target a (markedOrderedPrimeTuplePrefix t a)

def markedOrderedPrimeBefore {n : ℕ} (e : Fin n ≃o A) (i : Fin n)
    (b : {b : A // b<e i}) : Fin i.val :=
  ⟨(e.symm b.1).val,by simpa using e.symm.strictMono b.2⟩

def markedOrderedPrimeTarget {n : ℕ} (e : Fin n ≃o A)
    (target : (a : A) → ({b : A // b<a} → Nat.Primes) → Option Nat.Primes)
    (i : Fin n) (prior : Fin i.val → Nat.Primes) : Option Nat.Primes :=
  target (e i) (fun b => prior (markedOrderedPrimeBefore e i b))

def markedOrderedPrimeSelected {n : ℕ} (e : Fin n ≃o A) (S : Finset A) : Finset (Fin n) :=
  S.map e.symm.toEquiv.toEmbedding

theorem markedOrderedPrimeSelected_mem {n : ℕ} (e : Fin n ≃o A) (S : Finset A) (i : Fin n) :
    i∈markedOrderedPrimeSelected e S ↔ e i∈S := by
  simp [markedOrderedPrimeSelected]

theorem markedOrderedPrimeSelected_card {n : ℕ} (e : Fin n ≃o A) (S : Finset A) :
    (markedOrderedPrimeSelected e S).card=S.card := Finset.card_map _

theorem markedOrderedPrimeTuple_reindex_apply {n : ℕ} (e : Fin n ≃o A)
    (P : A → Finset Nat.Primes) (t : (i : Fin n) → ↥(P (e i))) (i : Fin n) :
    (Equiv.piCongrLeft (fun a => ↥(P a)) e.toEquiv t) (e i)=t i := by
  change (Equiv.piCongrLeft (fun a => ↥(P a)) e.toEquiv t) (e.toEquiv i)=t i
  exact Equiv.piCongrLeft_apply_apply (fun a => ↥(P a)) e.toEquiv t i

theorem markedOrderedPrimeTuplePrefix_reindex {n : ℕ} (e : Fin n ≃o A)
    (P : A → Finset Nat.Primes) (t : (i : Fin n) → ↥(P (e i))) (i : Fin n) :
    markedOrderedPrimeTuplePrefix (Equiv.piCongrLeft (fun a => ↥(P a)) e.toEquiv t) (e i)=
      (fun b => markedPrimeTuplePrefix t i (markedOrderedPrimeBefore e i b)) := by
  funext b
  change ((Equiv.piCongrLeft (fun a => ↥(P a)) e.toEquiv t) b.1).1=
    (t ⟨(e.symm b.1).val,_⟩).1
  have he : e (e.symm b.1)=b.1 := e.apply_symm_apply b.1
  conv_lhs => rw [← he,markedOrderedPrimeTuple_reindex_apply]

theorem markedOrderedPrimePrescribed_reindex {n : ℕ} (e : Fin n ≃o A)
    (P : A → Finset Nat.Primes) (S : Finset A)
    (target : (a : A) → ({b : A // b<a} → Nat.Primes) → Option Nat.Primes)
    (t : (i : Fin n) → ↥(P (e i))) :
    MarkedOrderedPrimeTuplePrescribed S target (Equiv.piCongrLeft (fun a => ↥(P a)) e.toEquiv t) ↔
      MarkedEarlierPrimeTuplePrescribed (markedOrderedPrimeSelected e S)
        (markedOrderedPrimeTarget e target) t := by
  constructor
  · intro h i hi
    have hh := h (e i) ((markedOrderedPrimeSelected_mem e S i).mp hi)
    rw [markedOrderedPrimeTuple_reindex_apply,markedOrderedPrimeTuplePrefix_reindex] at hh
    exact hh
  · intro h a ha
    obtain ⟨i,rfl⟩ := e.surjective a
    rw [markedOrderedPrimeTuple_reindex_apply,markedOrderedPrimeTuplePrefix_reindex]
    exact h i ((markedOrderedPrimeSelected_mem e S i).mpr ha)

theorem markedOrderedPrimeProduct_reindex [Fintype A] {n : ℕ} (e : Fin n ≃o A)
    (P : A → Finset Nat.Primes) (ν : (a : A) → ↥(P a) → ℝ)
    (t : (i : Fin n) → ↥(P (e i))) :
    (∏ a,ν a ((Equiv.piCongrLeft (fun a => ↥(P a)) e.toEquiv t) a))=
      ∏ i,ν (e i) (t i) := by
  rw [← e.toEquiv.prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

end
end ArtinMatthews
