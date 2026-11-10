module

public import ArtinMatthews.MarkedMemoryGhostInclude
public import ArtinMatthews.MarkedMemoryEdgeInclude
public import ArtinMatthews.MarkedMemoryHistoryWindow
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

/-! Exact chronological inclusion and restriction of a finite position
window. Every ghost mask, ordered birth tuple and both slot permutations
are retained. The image consists precisely of histories visiting the
smaller window at every vertex. -/

namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z W : Finset (ℤ × ℤ)} (h : Z ⊆ W)
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (hW : ∀ z ∈ W, IsCoprime z.1 z.2)

def markedMemoryHistoryInclude :
    (n : ℕ) → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s →
        MarkedMemoryChronologicalHistory hW n (markedRawStateInclude h s)
  | 0, s, H => markedMemoryGhostChoiceInclude h hZ hW s H
  | n+1, s, H =>
      ⟨markedMemoryGhostChoiceInclude h hZ hW s H.1,
        markedMemoryEdgeChoiceInclude h hZ hW
          (markedMemoryGhostChoiceTarget hZ s H.1) H.2.1,
        markedMemoryHistoryInclude n H.2.2⟩

theorem markedMemoryHistoryInclude_afterWindow (n : ℕ)
    {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    MarkedMemoryHistoryAfterWindow hW Z (markedMemoryHistoryInclude h hZ hW n H) := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih => exact ⟨H.2.1.2.1.target.2, ih H.2.2⟩

def markedMemoryHistoryRestrict :
    (n : ℕ) → (s : MarkedRawState P (pads+1) B Z) →
      (H : MarkedMemoryChronologicalHistory hW n (markedRawStateInclude h s)) →
        MarkedMemoryHistoryAfterWindow hW Z H → MarkedMemoryChronologicalHistory hZ n s
  | 0, s, H, _ => (markedMemoryGhostChoiceIncludeEquiv h hZ hW s).symm H
  | n+1, s, H, hH =>
      let ghost := (markedMemoryGhostChoiceIncludeEquiv h hZ hW s).symm H.1
      let edge := (markedMemoryEdgeChoiceWindowEquiv h hZ hW
        (markedMemoryGhostChoiceTarget hZ s ghost)).symm ⟨H.2.1, hH.1⟩
      ⟨ghost, edge, markedMemoryHistoryRestrict n
        (markedMemoryEdgeChoiceTarget hZ (markedMemoryGhostChoiceTarget hZ s ghost) edge)
        H.2.2 hH.2⟩

theorem markedMemoryHistoryRestrict_include (n : ℕ)
    {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryRestrict h hZ hW n s (markedMemoryHistoryInclude h hZ hW n H)
      (markedMemoryHistoryInclude_afterWindow h hZ hW n H) = H := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rcases H with ⟨ghost, edge, tail⟩
    exact congrArg
      (fun t => (⟨ghost, edge, t⟩ : MarkedMemoryChronologicalHistory hZ (n+1) s))
      (ih tail)

theorem markedMemoryHistoryInclude_restrict (n : ℕ)
    (s : MarkedRawState P (pads+1) B Z)
    (H : MarkedMemoryChronologicalHistory hW n (markedRawStateInclude h s))
    (hH : MarkedMemoryHistoryAfterWindow hW Z H) :
    markedMemoryHistoryInclude h hZ hW n (markedMemoryHistoryRestrict h hZ hW n s H hH) = H := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rcases H with ⟨ghost, edge, tail⟩
    let smallGhost := (markedMemoryGhostChoiceIncludeEquiv h hZ hW s).symm ghost
    let smallEdge := (markedMemoryEdgeChoiceWindowEquiv h hZ hW
      (markedMemoryGhostChoiceTarget hZ s smallGhost)).symm ⟨edge, hH.1⟩
    let smallTarget := markedMemoryEdgeChoiceTarget hZ
      (markedMemoryGhostChoiceTarget hZ s smallGhost) smallEdge
    exact congrArg
      (fun t => (⟨ghost, edge, t⟩ :
        MarkedMemoryChronologicalHistory hW (n+1) (markedRawStateInclude h s)))
      (ih smallTarget tail hH.2)

theorem markedMemoryHistoryInclude_target (n : ℕ)
    {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryChronologicalTarget hW (markedMemoryHistoryInclude h hZ hW n H) =
      markedRawStateInclude h (markedMemoryChronologicalTarget hZ H) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih H.2.2

theorem markedMemoryHistoryInclude_vertex (n : ℕ)
    {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1)) :
    markedMemoryHistoryVertexState hW (markedMemoryHistoryInclude h hZ hW n H) v =
      markedRawStateInclude h (markedMemoryHistoryVertexState hZ H v) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact Fin.cases rfl (fun w => ih H.2.2 w) v

theorem markedMemoryHistoryInclude_vertices (n : ℕ)
    {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    MarkedMemoryHistoryVerticesIn hW Z (markedMemoryHistoryInclude h hZ hW n H) := by
  intro v
  rw [markedMemoryHistoryInclude_vertex]
  exact (markedMemoryHistoryVertexState hZ H v).1.2

def markedMemoryHistoryWindowEquiv (n : ℕ) (s : MarkedRawState P (pads+1) B Z) :
    MarkedMemoryChronologicalHistory hZ n s ≃
      {H : MarkedMemoryChronologicalHistory hW n (markedRawStateInclude h s) //
        MarkedMemoryHistoryVerticesIn hW Z H} where
  toFun H := ⟨markedMemoryHistoryInclude h hZ hW n H,
    markedMemoryHistoryInclude_vertices h hZ hW n H⟩
  invFun H := markedMemoryHistoryRestrict h hZ hW n s H.1
    ((markedMemoryHistoryVerticesIn_iff hW H.1).mp H.2).2
  left_inv H := markedMemoryHistoryRestrict_include h hZ hW n H
  right_inv H := Subtype.ext (markedMemoryHistoryInclude_restrict h hZ hW n s H.1 _)

end
end ArtinMatthews
