module

public import ArtinMatthews.MarkedPhysicalCoordinateIndexCoefficient
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

/-! An actual chronological memory history determines the original
physical coordinate index: every ordered active list and both copied
slot permutations are retained. The initial coordinate remains e1. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
  {pads B R n : ℕ}
  (hZ : ∀ z∈markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2)
  {s : MarkedRawState (fun j => markedRawPrimeBand (P j)) (pads+1) B (markedPrimitiveCoordinateTube R)}
  (H : MarkedMemoryChronologicalHistory hZ n s)

def markedPhysicalMemoryHistoryIndex : MarkedPhysicalCoordinateIndex P (pads+1) n R :=
  (fun v => markedPhysicalMarkingEquiv P hP (pads+1) (markedMemoryHistoryVertexState hZ H v).2.1,
    (fun v => (markedMemoryHistoryVertexState hZ H v.succ).1,
      fun v => ((markedMemoryHistoryVertexEdge hZ H v).1,
        fun j => ((markedMemoryHistoryVertexEdge hZ H v).2.2 j).symm)))

omit [DecidableEq J] in
theorem markedPhysicalMemoryHistoryIndex_path (hs : s.1.1=(1,0)) (v : Fin (n+1)) :
    markedPhysicalCoordinateIndexPath (markedPhysicalMemoryHistoryIndex P hP hZ H).2.1 v=
      (markedMemoryHistoryVertexState hZ H v).1.1 := by
  cases v using Fin.cases with
  | zero =>
    simpa only [markedPhysicalMemoryHistoryIndex,markedPhysicalCoordinateIndexPath,Fin.cons_zero,
      markedMemoryHistoryVertexState_zero] using hs.symm
  | succ v => rfl

omit [DecidableEq J] in
theorem markedPhysicalMemoryHistoryIndex_distinct
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ H) (v : Fin (n+1)) :
    MarkedPhysicalMarkingDistinct ((markedPhysicalMemoryHistoryIndex P hP hZ H).1 v) := by
  apply (markedPhysicalMarkingEquiv_distinct P hP (pads+1) _).mpr
  intro j a b hab
  have hi := markedMemoryHistoryBirthDistinct_stage hZ H hempty hd (markedMemoryHistoryVertexStage n v)
  have he := hi (show markedMemoryPopulationPrime (markedMemoryHistoryVertexState hZ H v) (Sum.inl ⟨j,a⟩)=
    markedMemoryPopulationPrime (markedMemoryHistoryVertexState hZ H v) (Sum.inl ⟨j,b⟩) from
      congrArg (fun p => p.1) hab)
  exact eq_of_heq (Sigma.mk.inj (Sum.inl.inj he)).2

end
end ArtinMatthews
