module

public import ArtinMatthews.MarkedMemoryPrimeLifespanInterval
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

/-! A finite active path with its actual single-slot exchanges. The
incoming-not-source condition is the physical ban, retained explicitly;
no claim that an arbitrary sequence of lists has these properties is made. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] (P : J → Finset Nat.Primes)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (n : ℕ)

structure MarkedMemoryActivePathData where
  position : Fin (n+1) → Z
  active : Fin (n+1) → (j : J) → Fin (pads+1) ↪ ↥(P j)
  incoming : Fin n → (j : J) → ↥(P j)
  outgoing : Fin n → (j : J) → ↥(P j)
  outgoing_present : ∀ v j,∃ k,active v.castSucc j k=outgoing v j
  incoming_present : ∀ v j,∃ k,active v.succ j k=incoming v j
  incoming_not_source : ∀ v j,¬∃ k,active v.castSucc j k=incoming v j
  exchange : ∀ v j p,(∃ k,active v.succ j k=p) ↔
    ((∃ k,active v.castSucc j k=p) ∧ p≠outgoing v j) ∨ p=incoming v j

variable {P pads Z n}
  (d : MarkedMemoryActivePathData P pads Z n)

def markedMemoryPathVisits (j : J) (p : P j) : Finset (Fin (n+1)) :=
  Finset.univ.filter (fun v => ∃ k,d.active v j k=p)

omit [Fintype J] in
theorem markedMemoryPathVisits_mem (j : J) (p : P j) (v : Fin (n+1)) :
    v∈markedMemoryPathVisits d j p ↔ ∃ k,d.active v j k=p := by
  simp only [markedMemoryPathVisits,Finset.mem_filter,Finset.mem_univ,true_and]

omit [Fintype J] in
theorem markedMemoryPath_incoming_of_new (v : Fin n) (j : J) (p : P j)
    (hn : v.succ∈markedMemoryPathVisits d j p)
    (ho : v.castSucc∉markedMemoryPathVisits d j p) : p=d.incoming v j := by
  rcases (d.exchange v j p).mp ((markedMemoryPathVisits_mem d j p v.succ).mp hn) with h | h
  · exact False.elim (ho ((markedMemoryPathVisits_mem d j p v.castSucc).mpr h.1))
  · exact h

omit [Fintype J] in
theorem markedMemoryPath_outgoing_of_last (v : Fin n) (j : J) (p : P j)
    (ho : v.castSucc∈markedMemoryPathVisits d j p)
    (hn : v.succ∉markedMemoryPathVisits d j p) : p=d.outgoing v j := by
  by_contra hne
  apply hn
  apply (markedMemoryPathVisits_mem d j p v.succ).mpr
  exact (d.exchange v j p).mpr (Or.inl ⟨(markedMemoryPathVisits_mem d j p v.castSucc).mp ho,hne⟩)

omit [Fintype J] in
theorem markedMemoryPath_exchange_distinct (v : Fin n) (j : J) : d.incoming v j≠d.outgoing v j := by
  intro h
  apply d.incoming_not_source v j
  exact (d.outgoing_present v j).imp (fun k hk => hk.trans h.symm)

abbrev MarkedMemoryPathPrimeChoices := (j : J) → ↥(P j) → MarkedMemoryPrimeLifespanChoice n

def MarkedMemoryPathChoicesCompatible
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (c : MarkedMemoryPathPrimeChoices (P := P) (n := n)) : Prop :=
  ∀ j p,MarkedMemoryPrimeLifespanCompatible
    (fun v => markedPrimePositionLine (p.1:ℕ) (d.position v).1 (hZ _ (d.position v).2))
    (markedMemoryPathVisits d j p) (c j p)

abbrev MarkedMemoryPathUsedPrime (c : MarkedMemoryPathPrimeChoices (P := P) (n := n)) (j : J) :=
  {p : P j // MarkedMemoryPrimeLifespanUsed (markedMemoryPathVisits d j p) (c j p)}

instance markedMemoryPathUsedPrime_fintype
    (c : MarkedMemoryPathPrimeChoices (P := P) (n := n)) (j : J) :
    Fintype (MarkedMemoryPathUsedPrime d c j) := by infer_instance

end
end ArtinMatthews
