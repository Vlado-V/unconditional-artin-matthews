module

public import ArtinMatthews.MarkedMemoryHistoryChronological
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

/-! Assemble verified local transitions into an actual dependent
chronological history. This is only the finite assembly operation; the
independent lifespan adapters supply its choices and prove its links. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

def markedMemoryHistoryTransport {n : ℕ} {s t : MarkedRawState P (pads+1) B Z}
    (h : s = t) (history : MarkedMemoryChronologicalHistory hZ n s) :
    MarkedMemoryChronologicalHistory hZ n t := h ▸ history

theorem markedMemoryHistoryTransport_target {n : ℕ} {s t : MarkedRawState P (pads+1) B Z}
    (h : s = t) (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryChronologicalTarget hZ (markedMemoryHistoryTransport hZ h history) =
      markedMemoryChronologicalTarget hZ history := by
  cases h
  rfl

structure MarkedMemoryFiniteTransitions (N : ℕ) where
  state : (k : ℕ) → k ≤ N → MarkedRawState P (pads+1) B Z
  ghost : (k : ℕ) → (hk : k ≤ N) → MarkedMemoryGhostChoice hZ (state k hk)
  edge : (k : ℕ) → (hk : k < N) → MarkedMemoryEdgeChoice hZ
    (markedMemoryGhostChoiceTarget hZ (state k (Nat.le_of_lt hk)) (ghost k (Nat.le_of_lt hk)))
  link : ∀ k hk, markedMemoryEdgeChoiceTarget hZ
    (markedMemoryGhostChoiceTarget hZ (state k (Nat.le_of_lt hk)) (ghost k (Nat.le_of_lt hk)))
      (edge k hk) = state (k+1) hk

variable {N : ℕ} (d : MarkedMemoryFiniteTransitions (P := P) (pads := pads) (B := B) hZ N)

theorem markedMemoryFiniteTransitions_ghostTarget_congr
    (a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) (h : a = b) :
    markedMemoryGhostChoiceTarget hZ (d.state a ha) (d.ghost a ha) =
      markedMemoryGhostChoiceTarget hZ (d.state b hb) (d.ghost b hb) := by
  subst b
  rfl

def markedMemoryFiniteTransitions_segment : (remaining start : ℕ) → (hbound : start + remaining ≤ N) →
    MarkedMemoryChronologicalHistory hZ remaining (d.state start (by omega))
  | 0, start, _ => d.ghost start (by omega)
  | remaining+1, start, hbound =>
      ⟨d.ghost start (by omega), d.edge start (by omega),
        markedMemoryHistoryTransport hZ (d.link start (by omega)).symm
          (markedMemoryFiniteTransitions_segment remaining (start+1) (by omega))⟩

theorem markedMemoryFiniteTransitions_segment_zero (start : ℕ) (hbound : start+0 ≤ N) :
    markedMemoryFiniteTransitions_segment hZ d 0 start hbound = d.ghost start (by omega) := rfl

theorem markedMemoryFiniteTransitions_segment_succ (remaining start : ℕ) (hbound : start+(remaining+1) ≤ N) :
    markedMemoryFiniteTransitions_segment hZ d (remaining+1) start hbound =
      ⟨d.ghost start (by omega), d.edge start (by omega),
        markedMemoryHistoryTransport hZ (d.link start (by omega)).symm
          (markedMemoryFiniteTransitions_segment hZ d remaining (start+1) (by omega))⟩ := rfl

theorem markedMemoryFiniteTransitions_segment_target (remaining start : ℕ) (hbound : start + remaining ≤ N) :
    markedMemoryChronologicalTarget hZ (markedMemoryFiniteTransitions_segment hZ d remaining start hbound) =
      markedMemoryGhostChoiceTarget hZ (d.state (start+remaining) hbound) (d.ghost (start+remaining) hbound) := by
  induction remaining generalizing start with
  | zero => rfl
  | succ remaining ih =>
    have hn : start + 1 + remaining ≤ N := by omega
    change markedMemoryChronologicalTarget hZ
      (markedMemoryHistoryTransport hZ (d.link start (by omega)).symm
        (markedMemoryFiniteTransitions_segment hZ d remaining (start+1) hn)) = _
    rw [markedMemoryHistoryTransport_target]
    exact (ih (start+1) hn).trans
      (markedMemoryFiniteTransitions_ghostTarget_congr hZ d _ _ hn hbound (by omega))

/-- Local target equalities suffice to construct the entire actual
history, including its final ghost operation. -/
theorem markedMemoryFiniteTransitions_exists (remaining start : ℕ) (hbound : start + remaining ≤ N) :
    ∃ history : MarkedMemoryChronologicalHistory hZ remaining (d.state start (by omega)),
      markedMemoryChronologicalTarget hZ history =
        markedMemoryGhostChoiceTarget hZ (d.state (start+remaining) hbound) (d.ghost (start+remaining) hbound) :=
  ⟨markedMemoryFiniteTransitions_segment hZ d remaining start hbound,
    markedMemoryFiniteTransitions_segment_target hZ d remaining start hbound⟩

def markedMemoryFiniteTransitions_history :
    MarkedMemoryChronologicalHistory hZ N (d.state 0 (Nat.zero_le N)) :=
  markedMemoryFiniteTransitions_segment hZ d N 0 (by omega)

theorem markedMemoryFiniteTransitions_history_target :
    markedMemoryChronologicalTarget hZ (markedMemoryFiniteTransitions_history hZ d) =
      markedMemoryGhostChoiceTarget hZ (d.state N (Nat.le_refl N)) (d.ghost N (Nat.le_refl N)) :=
  (markedMemoryFiniteTransitions_segment_target hZ d N 0 (by omega)).trans
    (markedMemoryFiniteTransitions_ghostTarget_congr hZ d (0+N) N (by omega) (Nat.le_refl N) (by omega))

end
end ArtinMatthews
