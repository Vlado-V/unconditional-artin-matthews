module

public import ArtinMatthews.MarkedMemoryActualSlotOrder
public import ArtinMatthews.MarkedMemoryIndependentHistory
public import ArtinMatthews.MarkedMemoryIndependentMarks
public import ArtinMatthews.MarkedMemoryActualHistoryReconstruction
public import ArtinMatthews.MarkedMemoryEndpointGuardData
public import ArtinMatthews.MarkedMemoryIndependentEndpointGuards
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

/-! The inverse capped-path construction obtains its local guards from
the actual original history and its empty boundary memories. Numeric
prime injectivity is derived from performed-birth distinctness. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  {s : MarkedRawState P (pads+1) B Z} (H : MarkedMemoryChronologicalHistory hZ n s)
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ H)

theorem markedMemoryActualCapped_initial
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0) (j : J) :
    ((markedMemoryActualTableau hZ H ha).lifespan j).initial=[] := by
  apply markedMemoryIndependent_initial_empty_of_sizes hZ (markedMemoryActualTableau hZ H ha)
  intro i
  exact (congrArg (fun u : MarkedRawState P (pads+1) B Z => (u.2.2.1.1 i:ℕ))
    (markedMemoryActualTableau_initial hZ H ha)).trans (hempty i)

theorem markedMemoryActualCapped_anchor :
    MarkedMemoryHistoryAnchorAdmissible hZ (markedMemoryIndependentHistory hZ
      (markedMemoryActualTableau hZ H ha) (markedMemoryActualOrder hZ H ha)) := by
  have hr := markedMemoryActualHistory_reconstruction hZ H ha
  have he := congrArg (MarkedMemoryHistoryAnchorAdmissible hZ) hr
  exact (markedMemoryHistoryAnchor_transport hZ (markedMemoryActualTableau_initial hZ H ha) _).mp (Eq.mpr he ha)

theorem markedMemoryActualCapped_terminal
    (ht : ∀ j,((markedMemoryChronologicalTarget hZ H).2.2.1.1 j:ℕ)=0) (j : J) :
    markedMemoryIndependentQueue hZ (markedMemoryActualTableau hZ H ha) (2*n+1) j=[] := by
  apply markedMemoryIndependent_terminal_empty_of_sizes hZ (markedMemoryActualTableau hZ H ha)
    (markedMemoryActualOrder hZ H ha)
  intro i
  have he := markedMemoryHistoryTransport_target hZ (markedMemoryActualTableau_initial hZ H ha)
    (markedMemoryIndependentHistory hZ (markedMemoryActualTableau hZ H ha) (markedMemoryActualOrder hZ H ha))
  have hr := congrArg (markedMemoryChronologicalTarget hZ) (markedMemoryActualHistory_reconstruction hZ H ha)
  exact (congrArg (fun u : MarkedRawState P (pads+1) B Z => (u.2.2.1.1 i:ℕ)) (he.symm.trans hr)).trans (ht i)

theorem markedMemoryActualCapped_prime_injective
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0) (hd : MarkedMemoryHistoryBirthDistinct hZ H) :
    Function.Injective (markedMemoryIndependentPrime hZ (markedMemoryActualTableau hZ H ha)) := by
  have hr := markedMemoryActualHistory_reconstruction hZ H ha
  have he := congrArg (MarkedMemoryHistoryBirthDistinct hZ) hr
  have hb := (markedMemoryHistoryBirthDistinct_transport hZ (markedMemoryActualTableau_initial hZ H ha) _).mp
    (Eq.mpr he hd)
  exact markedMemoryIndependentPrime_injective_of_birthDistinct hZ (markedMemoryActualTableau hZ H ha)
    (markedMemoryActualOrder hZ H ha) (markedMemoryActualCapped_initial hZ H ha hempty) hb

end
end ArtinMatthews
