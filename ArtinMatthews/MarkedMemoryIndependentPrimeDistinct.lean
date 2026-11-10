module

public import ArtinMatthews.MarkedMemoryHistoryBirths
public import ArtinMatthews.MarkedMemoryIndependentHistory
public import ArtinMatthews.MarkedMemoryIndependentMarks
public import ArtinMatthews.MarkedMemoryInitialMeasure
public import ArtinMatthews.MarkedMemoryUsedBaseline
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

/-! With empty initial memory, injective numeric labels on the actual
independent identities imply performed-birth distinctness. This is the
converse direction needed for a one-lifespan-per-prime construction. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

theorem markedMemoryIndependent_birthDistinct_of_prime_injective
    (hempty : ∀ j,(d.lifespan j).initial=[])
    (hinj : Function.Injective (markedMemoryIndependentPrime hZ d)) :
    MarkedMemoryHistoryBirthDistinct hZ (markedMemoryIndependentHistory hZ d order) := by
  let H := markedMemoryIndependentHistory hZ d order
  have hs : ∀ j,((markedMemoryIndependentState hZ d 0 (Nat.zero_le n)).2.2.1.1 j:ℕ)=0 := by
    intro j
    change ((markedMemoryIndependentMemory hZ d 0 (by omega)).1.1 j:ℕ)=0
    rw [markedMemory_initial_memory_empty hZ d hempty]
    rfl
  have ht : Function.Injective (markedMemoryHistoryTraceAddressPrime hZ H) := by
    intro a b hab
    apply (markedMemoryIndependentAddressEquiv hZ d order).injective
    apply hinj
    exact (markedMemoryIndependentAddress_prime hZ d order a).trans
      (hab.trans (markedMemoryIndependentAddress_prime hZ d order b).symm)
  let e := markedMemoryHistoryTraceAddressEquiv hZ H hs
  intro a b hab
  apply e.symm.injective
  apply ht
  have ha := markedMemoryHistoryTraceAddressEquiv_prime hZ H hs (e.symm a)
  have hb := markedMemoryHistoryTraceAddressEquiv_prime hZ H hs (e.symm b)
  rw [e.apply_symm_apply] at ha hb
  exact ha.symm.trans (hab.trans hb)

theorem markedMemoryIndependent_birthDistinct_iff_prime_injective
    (hempty : ∀ j,(d.lifespan j).initial=[]) :
    MarkedMemoryHistoryBirthDistinct hZ (markedMemoryIndependentHistory hZ d order) ↔
      Function.Injective (markedMemoryIndependentPrime hZ d) :=
  ⟨markedMemoryIndependentPrime_injective_of_birthDistinct hZ d order hempty,
    markedMemoryIndependent_birthDistinct_of_prime_injective hZ d order hempty⟩

end
end ArtinMatthews
