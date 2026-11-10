module

public import ArtinMatthews.MarkedMemoryIndependentHistory
public import ArtinMatthews.MarkedRawBoundary
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! Nonzero literal terminal boundary forces the independent terminal
queues to be empty. This is extracted from the actual raw target, not
supplied as a primewise endpoint condition. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads)) (z₀ : Z)

local notation "H" => markedMemoryIndependentHistory hZ d order

theorem markedMemoryIndependent_terminal_queue_of_boundary_ne_zero
    (hb : markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ H)≠0) (j : J) :
    markedMemoryIndependentQueue hZ d (2*n+1) j=[] := by
  have he : (markedMemoryChronologicalTarget hZ H).2.2=markedRawBoundaryEmptyMemory P B := by
    by_contra hn
    apply hb
    simp only [markedRawBoundary,hn,and_false,ite_false]
  have ht := congrArg (fun u : MarkedRawState P (pads+1) B Z => u.2.2)
    (markedMemoryIndependentHistory_target hZ d order)
  have hm : markedMemoryIndependentMemory hZ d (2*n+1) (by omega)=markedRawBoundaryEmptyMemory P B :=
    ht.symm.trans he
  have hl := congrArg (fun m : MarkedRawMemory P B => List.ofFn (m.2 j)) hm
  rw [markedMemoryIndependentMemory,markedMemoryLabeledQueueState_list] at hl
  change (markedMemoryIndependentQueue hZ d (2*n+1) j).map (d.particle j)=[] at hl
  exact List.map_eq_nil_iff.mp hl

end
end ArtinMatthews
