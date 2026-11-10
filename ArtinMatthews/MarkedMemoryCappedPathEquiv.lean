module

public import ArtinMatthews.MarkedMemoryCappedPathAssembly
public import ArtinMatthews.MarkedMemoryActualCappedLift
public import ArtinMatthews.MarkedMemoryCappedPathInjective
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

/-! The actual finite capped path/decorations carrier is equivalent to
the supported original history carrier. Canonical used-prime labels
give exactly one preimage, rather than an assumed labeling quotient. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (hP : ∀ i j,i≠j → Disjoint (P i) (P j))
  (s : MarkedRawState P (pads+1) B Z) (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)

def markedMemoryCappedPathEquiv :
    MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s ≃ MarkedMemoryPrimeSupportedHistory (n := n) hZ s :=
  Equiv.ofBijective (markedMemoryCappedPathSupportedAssembly hZ hP s)
    ⟨fun _ _ h => markedMemoryCappedPathDecoratedAssembly_injective hZ hP s hempty (congrArg Subtype.val h),
      markedMemoryCappedPathSupportedAssembly_surjective hZ s hempty hP⟩

theorem markedMemoryCappedPathEquiv_apply
    (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s) :
    (markedMemoryCappedPathEquiv hZ hP s hempty i).1=markedMemoryCappedPathDecoratedAssembly hZ hP s i := rfl

include hempty in
theorem markedMemoryCappedPath_actual_fiber_card
    (H : MarkedMemoryPrimeSupportedHistory (n := n) hZ s) :
    Fintype.card {i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s //
      markedMemoryCappedPathDecoratedAssembly hZ hP s i=H.1}=1 := by
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨markedMemoryActualCappedLift hZ s hempty H,
    markedMemoryActualCappedLift_reconstruction hZ s hempty hP H⟩,?_⟩
  intro i
  apply Subtype.ext
  apply markedMemoryCappedPathDecoratedAssembly_injective hZ hP s hempty
  exact i.2.trans (markedMemoryActualCappedLift_reconstruction hZ s hempty hP H).symm

include hempty in
theorem markedMemoryCappedPath_supported_sum {R : Type*} [AddCommMonoid R]
    (F : MarkedMemoryChronologicalHistory hZ n s → R) :
    (∑ H : MarkedMemoryPrimeSupportedHistory (n := n) hZ s,F H.1)=
      ∑ i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s,
        F (markedMemoryCappedPathDecoratedAssembly hZ hP s i) :=
  (Equiv.sum_comp (markedMemoryCappedPathEquiv hZ hP s hempty) (fun H => F H.1)).symm

end
end ArtinMatthews
