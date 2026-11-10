module

public import ArtinMatthews.MarkedMemoryHistoryDistinct
public import ArtinMatthews.MarkedMemoryTiltPrimewise
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

/-! Literal active visits of an indexed chronological identity. The visit
set agrees with the existing primewise expansion only after the actual
global birth-distinct condition and empty initial memory are imposed. -/
namespace ArtinMatthews
noncomputable section

def markedMemoryHistoryVertexStage : (n : ℕ) → Fin (n+1) → MarkedMemoryHistoryStage n
  | 0,_ => false
  | n+1,v => Fin.cases (Sum.inl ())
      (fun j => Sum.inr (Sum.inr (markedMemoryHistoryVertexStage n j))) v

def markedMemoryHistoryVertexState {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1)) : MarkedRawState P (pads+1) B Z :=
  markedMemoryHistoryStageState hZ history (markedMemoryHistoryVertexStage n v)

/-- Actual initial-active or performed-birth identity; it is not a prime quotient. -/
abbrev MarkedMemoryHistoryAddress {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :=
  (Σ _j : J, Fin (pads+1)) ⊕ MarkedMemoryHistoryBirths hZ history

def markedMemoryHistoryAddressPrime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) : MarkedMemoryHistoryAddress hZ history → Nat.Primes :=
  Sum.elim (fun a => (s.2.1 a.1 a.2).1) (markedMemoryHistoryBirthPrime hZ history)

def markedMemoryHistoryIdentityVisits {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hempty : ∀ j, (s.2.2.1.1 j : ℕ)=0)
    (a : MarkedMemoryHistoryAddress hZ history) : Finset (Fin (n+1)) := by
  classical
  exact Finset.univ.filter (fun v => ∃ j k,
    markedMemoryHistoryStageBirthOrigin hZ history hempty (markedMemoryHistoryVertexStage n v)
      (Sum.inl ⟨j,k⟩) = a)

/-- An actual active slot has a given prime exactly when its literal indexed
birth identity is that prime's unique history address. -/
theorem markedMemoryHistory_active_prime_iff_origin {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hempty : ∀ j, (s.2.2.1.1 j : ℕ)=0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history) (v : Fin (n+1)) (j : J) (k : Fin (pads+1))
    (a : MarkedMemoryHistoryAddress hZ history) :
    ((markedMemoryHistoryVertexState hZ history v).2.1 j k).1 = markedMemoryHistoryAddressPrime hZ history a ↔
      markedMemoryHistoryStageBirthOrigin hZ history hempty (markedMemoryHistoryVertexStage n v)
        (Sum.inl ⟨j,k⟩) = a := by
  have hp := markedMemoryHistoryStageBirthOrigin_prime hZ history hempty
    (markedMemoryHistoryVertexStage n v) (Sum.inl ⟨j,k⟩)
  constructor
  · intro h
    apply hd
    exact hp.trans h
  · intro h
    exact hp.symm.trans (congrArg (markedMemoryHistoryAddressPrime hZ history) h)

/-- Exact identification of the indexed active-visit set with the literal
prime occurrence set consumed by the primewise lifespan expansion. -/
theorem markedMemoryHistory_identity_visits_eq {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hempty : ∀ j, (s.2.2.1.1 j : ℕ)=0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history) (a : MarkedMemoryHistoryAddress hZ history) :
    markedMemoryHistoryIdentityVisits hZ history hempty a =
      markedMemoryActiveVisits (fun v => (markedMemoryHistoryVertexState hZ history v).2.1)
        (markedMemoryHistoryAddressPrime hZ history a) := by
  classical
  ext v
  simp only [markedMemoryHistoryIdentityVisits, markedMemoryActiveVisits,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact exists_congr (fun j => exists_congr (fun k =>
    (markedMemoryHistory_active_prime_iff_origin hZ history hempty hd v j k a).symm))

end
end ArtinMatthews
