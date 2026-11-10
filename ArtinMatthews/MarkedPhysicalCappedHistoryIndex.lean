module

public import ArtinMatthews.MarkedMemoryCappedPathAssembly
public import ArtinMatthews.MarkedPhysicalActivePathIndex
public import ArtinMatthews.MarkedPhysicalMemoryHistoryIndex
public import ArtinMatthews.MarkedMemoryCappedPathIndependent
public import ArtinMatthews.MarkedMemoryCappedPathRecovery
public import ArtinMatthews.MarkedMemoryEndpointGuardData
public import ArtinMatthews.MarkedPhysicalHistoryIndexIndependent
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! For a canonical capped prime path, the coordinate index depends only
on the original active path and its free copied ordering. All ghost-birth
enumerations and optional prime endpoints disappear from this index. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
  (hdis : ∀ j k,j≠k → Disjoint (markedRawPrimeBand (P j)) (markedRawPrimeBand (P k)))
  {pads B R n : ℕ}
  (hZ : ∀ z∈markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2)
  (s : MarkedRawState (fun j => markedRawPrimeBand (P j)) (pads+1) B (markedPrimitiveCoordinateTube R))

omit [DecidableEq J] in
theorem markedPhysicalCappedHistoryIndex_eq
    (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s) :
    markedPhysicalMemoryHistoryIndex P hP hZ (markedMemoryCappedPathDecoratedAssembly hZ hdis s i)=
      markedPhysicalActivePathIndex P hP i.1.path i.2.2 := by
  unfold markedMemoryCappedPathDecoratedAssembly
  rw [markedPhysicalMemoryHistoryIndex_transport,
    markedPhysicalMemoryHistoryIndex_independent P hP hZ _
      (markedMemoryCappedPathIndependent_prime_injective (B := B) hZ i.1.path i.1.choices
        i.1.compatible i.1.capacity i.2.1 hdis)]
  rw [markedMemoryCappedPathIndependent_path (B := B) hZ i.1.path i.1.choices i.1.compatible
    i.1.capacity i.2.1 hdis]

omit [DecidableEq J] in
theorem markedPhysicalCappedHistory_target_position
    (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s) :
    (markedMemoryChronologicalTarget hZ (markedMemoryCappedPathDecoratedAssembly hZ hdis s i)).1=
      i.1.path.position (Fin.last n) := by
  unfold markedMemoryCappedPathDecoratedAssembly
  rw [markedMemoryHistoryTransport_target,markedMemoryIndependentHistory_target]
  exact markedMemoryCappedPathIndependent_position hZ i.1.path i.1.choices i.1.compatible
    i.1.capacity i.2.1 (Fin.last n)

omit [DecidableEq J] in
theorem markedPhysicalCappedHistory_boundary
    (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s)
    (z₀ : ↥(markedPrimitiveCoordinateTube R)) :
    markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ
      (markedMemoryCappedPathDecoratedAssembly hZ hdis s i))=
      if i.1.path.position (Fin.last n)=z₀ then 1 else 0 := by
  have hm : (markedMemoryChronologicalTarget hZ
      (markedMemoryCappedPathDecoratedAssembly hZ hdis s i)).2.2=markedRawBoundaryEmptyMemory _ B :=
    (markedMemoryRawMemory_empty_iff_sizes _).mpr
      (markedMemoryCappedPathDecoratedAssembly_target_empty hZ hdis s i)
  unfold markedRawBoundary
  rw [markedPhysicalCappedHistory_target_position,hm]
  simp only [and_true]

end
end ArtinMatthews
