module

public import ArtinMatthews.MarkedMemoryHistoryInclude
public import ArtinMatthews.MarkedBirthDistinctPermutation
public import ArtinMatthews.MarkedMemoryPotentialBirths
public import ArtinMatthews.MarkedMemoryPotentialDistinct
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

/-! Window inclusion preserves every performed and unperformed potential
birth address literally, including the initial active tuple. Consequently
the original global birth-distinct guard and all permutation events are
unchanged, without any prime-injectivity premise. -/

namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z W : Finset (ℤ × ℤ)} (h : Z ⊆ W)
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (hW : ∀ z ∈ W, IsCoprime z.1 z.2)

theorem markedMemoryHistoryInclude_ghostValue (n : ℕ)
    {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1)) (j : J) (k : Fin B) :
    markedMemoryPotentialGhostValue hW (markedMemoryHistoryInclude h hZ hW n H) v j k =
      markedMemoryPotentialGhostValue hZ H v j k := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact Fin.cases rfl (fun w => ih H.2.2 w) v

theorem markedMemoryHistoryInclude_edgeValue (n : ℕ)
    {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n) (j : J) :
    markedMemoryPotentialEdgeValue hW (markedMemoryHistoryInclude h hZ hW n H) v j =
      markedMemoryPotentialEdgeValue hZ H v j := by
  induction n generalizing s with
  | zero => exact Fin.elim0 v
  | succ n ih => exact Fin.cases rfl (fun w => ih H.2.2 w) v

theorem markedMemoryHistoryInclude_potentialValues (n : ℕ)
    {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryPotentialAddressValue hW (markedMemoryHistoryInclude h hZ hW n H) =
      markedMemoryPotentialAddressValue hZ H := by
  funext a
  rcases a with ⟨j,k⟩ | (⟨v,j,k⟩ | ⟨v,j⟩)
  · rfl
  · exact markedMemoryHistoryInclude_ghostValue h hZ hW n H v j k
  · exact markedMemoryHistoryInclude_edgeValue h hZ hW n H v j

theorem markedMemoryHistoryInclude_birthDistinct_iff (n : ℕ)
    {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    MarkedMemoryHistoryBirthDistinct hW (markedMemoryHistoryInclude h hZ hW n H) ↔
      MarkedMemoryHistoryBirthDistinct hZ H := by
  rw [markedMemoryHistoryBirthDistinct_iff_potential,
    markedMemoryHistoryBirthDistinct_iff_potential,
    markedMemoryHistoryInclude_potentialValues]

theorem markedMemoryHistoryInclude_permutationEvent_iff (n : ℕ)
    {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n)) :
    MarkedBirthPermutationEvent
        (markedMemoryPotentialAddressValue hW (markedMemoryHistoryInclude h hZ hW n H)) σ ↔
      MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ H) σ := by
  rw [markedMemoryHistoryInclude_potentialValues]

end
end ArtinMatthews
