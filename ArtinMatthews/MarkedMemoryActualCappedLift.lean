module

public import ArtinMatthews.MarkedMemoryIndependentCappedLift
public import ArtinMatthews.MarkedMemoryActualCappedPrerequisites
public import ArtinMatthews.MarkedMemoryActualHistoryReconstruction
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

/-! Every actual supported history has a computed capped path with its
original birth and copied-slot decorations. The reconstructed history
is exactly the input history. No image-coverage premise is supplied. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (s : MarkedRawState P (pads+1) B Z) (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)

def markedMemoryActualCappedLift
    (H : MarkedMemoryPrimeSupportedHistory (n := n) hZ s) :
    MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s :=
  markedMemoryIndependentCappedLift hZ (markedMemoryActualTableau hZ H.1 H.2.1)
    (markedMemoryActualCapped_prime_injective hZ H.1 H.2.1 hempty H.2.2.1)
    (markedMemoryActualCapped_initial hZ H.1 H.2.1 hempty)
    (markedMemoryActualCapped_terminal hZ H.1 H.2.1 H.2.2.2)
    (markedMemoryActualTableau_birthNormalized hZ H.1 hempty H.2.1)
    (markedMemoryActualOrder hZ H.1 H.2.1)
    (markedMemoryActualCapped_anchor hZ H.1 H.2.1) s
    (markedMemoryActualTableau_initial hZ H.1 H.2.1)

theorem markedMemoryActualCappedLift_reconstruction
    (hP : ∀ i j,i≠j → Disjoint (P i) (P j))
    (H : MarkedMemoryPrimeSupportedHistory (n := n) hZ s) :
    markedMemoryCappedPathDecoratedAssembly hZ hP s (markedMemoryActualCappedLift hZ s hempty H)=H.1 := by
  have hi := markedMemoryIndependentCappedLift_history hZ (markedMemoryActualTableau hZ H.1 H.2.1)
    (markedMemoryActualCapped_prime_injective hZ H.1 H.2.1 hempty H.2.2.1)
    (markedMemoryActualCapped_initial hZ H.1 H.2.1 hempty)
    (markedMemoryActualCapped_terminal hZ H.1 H.2.1 H.2.2.2)
    (markedMemoryActualTableau_birthNormalized hZ H.1 hempty H.2.1)
    (markedMemoryActualOrder hZ H.1 H.2.1)
    (markedMemoryActualCapped_anchor hZ H.1 H.2.1) s
    (markedMemoryActualTableau_initial hZ H.1 H.2.1) hP
  exact hi.trans (markedMemoryActualHistory_reconstruction hZ H.1 H.2.1)

include hempty in
theorem markedMemoryCappedPathSupportedAssembly_surjective
    (hP : ∀ i j,i≠j → Disjoint (P i) (P j)) :
    Function.Surjective (markedMemoryCappedPathSupportedAssembly (n := n) hZ hP s) := by
  intro H
  refine ⟨markedMemoryActualCappedLift hZ s hempty H,?_⟩
  apply Subtype.ext
  exact markedMemoryActualCappedLift_reconstruction hZ s hempty hP H

end
end ArtinMatthews
