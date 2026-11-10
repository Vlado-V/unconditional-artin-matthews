module

public import ArtinMatthews.MarkedMemoryHistoryAnchorGates
public import ArtinMatthews.MarkedMemoryIndependentHistory
public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess
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

/-! A finite vertex criterion for the literal chronological anchor gate.
The criterion uses actual local edges and is compatible with the source
transports in the independent transition assembler. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

theorem markedMemoryEdgeAnchorGate_heq
    {s t : MarkedRawState P (pads+1) B Z} (hs : s=t)
    (a : MarkedMemoryEdgeChoice hZ s) (b : MarkedMemoryEdgeChoice hZ t) (he : HEq a b) :
    MarkedMemoryEdgeAnchorGate hZ s a ↔ MarkedMemoryEdgeAnchorGate hZ t b := by
  cases hs
  cases eq_of_heq he
  rfl

theorem markedMemoryEdgeTransport_anchorGate
    {s t : MarkedRawState P (pads+1) B Z} (hs : s=t)
    (a : MarkedMemoryEdgeChoice hZ s) :
    MarkedMemoryEdgeAnchorGate hZ t (markedMemoryEdgeTransport hZ hs a) ↔
      MarkedMemoryEdgeAnchorGate hZ s a := by
  cases hs
  rfl

theorem markedMemoryHistoryAnchorAdmissible_iff_vertices
    {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    MarkedMemoryHistoryAnchorAdmissible hZ H ↔
      ∀ v : Fin n,MarkedMemoryEdgeAnchorGate hZ _ (markedMemoryHistoryVertexEdge hZ H v) := by
  induction n generalizing s with
  | zero => exact ⟨fun _ v => Fin.elim0 v,fun _ => trivial⟩
  | succ n ih =>
    constructor
    · rintro ⟨h0,ht⟩ v
      refine Fin.cases ?_ (fun w => ?_) v
      · exact h0
      · exact (ih H.2.2).mp ht w
    · intro hv
      exact ⟨hv 0,(ih H.2.2).mpr (fun w => hv w.succ)⟩

end
end ArtinMatthews
