module

public import ArtinMatthews.MarkedMemoryFiniteTableau
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

/-! Projection formulas for canonical extension, stated on an abstract
finite tableau so later concrete-cap adapters need no large reductions. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (f : MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n)

theorem markedMemoryFiniteProjection_initial (j : J) :
    ((markedMemoryFiniteTableau_toIndependent hZ f).lifespan j).initial=
      markedMemoryFiniteList_toList (f.1.initial j) := rfl

theorem markedMemoryFiniteProjection_first (j : J) (a : A j) :
    ((markedMemoryFiniteTableau_toIndependent hZ f).lifespan j).first a=(f.1.first j a).val := rfl

theorem markedMemoryFiniteProjection_last (j : J) (a : A j) :
    ((markedMemoryFiniteTableau_toIndependent hZ f).lifespan j).last a=(f.1.last j a).val := rfl

theorem markedMemoryFiniteProjection_particle (j : J) (a : A j) :
    (markedMemoryFiniteTableau_toIndependent hZ f).particle j a=f.1.particle j a := rfl

theorem markedMemoryFiniteProjection_position (v : Fin (n+1)) :
    (markedMemoryFiniteTableau_toIndependent hZ f).position v.val=f.1.position v := f.1.positionAt_valid v

theorem markedMemoryFiniteProjection_activeId (v : Fin (n+1)) (j : J) (k : Fin (pads+1)) :
    (markedMemoryFiniteTableau_toIndependent hZ f).activeId v.val j k=f.1.activeId v j k :=
  congrArg (fun e => e k) (f.1.activeIdAt_valid v j)

theorem markedMemoryFiniteProjection_incoming (v : Fin n) (j : J) :
    ((markedMemoryFiniteTableau_toIndependent hZ f).lifespan j).incoming (2*v.val+1)=f.1.incoming v j :=
  f.1.incomingAt_valid v j

theorem markedMemoryFiniteProjection_outgoing (v : Fin n) (j : J) :
    ((markedMemoryFiniteTableau_toIndependent hZ f).lifespan j).outgoing (2*v.val+1)=f.1.outgoing v j :=
  f.1.outgoingAt_valid v j

theorem markedMemoryFiniteProjection_queue_length [∀ j,DecidableEq (A j)]
    (t : ℕ) (ht : t≤2*n+1) (j : J) :
    (markedMemoryIndependentQueue hZ (markedMemoryFiniteTableau_toIndependent hZ f) t j).length=
      (f.1.pendingAt t j).card :=
  markedMemoryPendingQueueAt_length ((markedMemoryFiniteTableau_toIndependent hZ f).lifespan j) t ht

end
end ArtinMatthews
