module

public import ArtinMatthews.MarkedMemoryPivotValueDefs
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

/-! A recursive record of the actual chronological pivot tests. The
memo update is performed before checking the current stage, and every
later stage receives exactly that updated memo. -/

noncomputable section
namespace ArtinMatthews

def MarkedMemoryStageValueGate
    {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (stage : ℕ)
    (v : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes) : Prop :=
  ∀ a∈markedMemoryStageNonpivots σ stage,v a≠none ∧ v a=v (markedMemoryPotentialPivot σ a)

def MarkedMemoryPivotCompatible
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B N : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) :
    (n j : ℕ) → {s : MarkedRawState P (pads+1) B Z} → MarkedMemoryChronologicalHistory hZ n s →
      (MarkedMemoryPotentialAddress J (pads+1) B N → Option Nat.Primes) → Prop
  | 0,j,_,h,old => ∃ hg : j<N+1,
      MarkedMemoryStageValueGate σ (2*j+1) (markedMemoryGhostPivotValues ⟨j,hg⟩ old h.sizes.1 h.births)
  | n+1,j,s,h,old => ∃ hg : j<N+1,
      let afterGhost := markedMemoryGhostPivotValues ⟨j,hg⟩ old h.1.sizes.1 h.1.births
      let source := markedRawSlotEquiv h.2.1.1 (markedMemoryGhostChoiceTarget hZ s h.1)
      MarkedMemoryStageValueGate σ (2*j+1) afterGhost ∧ ∃ he : j<N,
        let afterEdge := markedMemoryEdgePivotValues ⟨j,he⟩ afterGhost hZ source h.2.1.2.1
        MarkedMemoryStageValueGate σ (2*j+2) afterEdge ∧
          MarkedMemoryPivotCompatible hZ σ n (j+1) h.2.2 afterEdge

end ArtinMatthews
