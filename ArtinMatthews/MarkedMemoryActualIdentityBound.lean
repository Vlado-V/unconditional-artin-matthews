module

public import ArtinMatthews.MarkedMemoryActualFibers
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

/-! A uniform finite bound on actual identity labels, from the indexed
initial population and performed births. Numeric primes need not differ. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)

theorem markedMemoryGhostBirthIndex_card_le {s : MarkedRawState P (pads+1) B Z}
    (ghost : MarkedMemoryGhostChoice hZ s) : Fintype.card (MarkedMemoryGhostBirthIndex ghost) ≤ B := by
  change Fintype.card (Σ j,Fin (ghost.sizes.1 j : ℕ)) ≤ B
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Finset.sum_le_sum (fun j _ => Nat.le_add_left (ghost.sizes.1 j : ℕ)
    (markedRawGhostSurvivors s.2.2 ghost.deletion j).card)).trans ghost.sizes.2

theorem markedMemoryEdgeBirthIndex_card_le {s : MarkedRawState P (pads+1) B Z}
    (edge : MarkedMemoryEdgeChoice hZ s) : Fintype.card (MarkedMemoryEdgeBirthIndex edge) ≤ Fintype.card J :=
  Fintype.card_subtype_le _

theorem markedMemoryPopulationIndex_card_le (s : MarkedRawState P (pads+1) B Z) :
    Fintype.card (MarkedMemoryPopulationIndex s) ≤ Fintype.card J * (pads+1) + B := by
  change Fintype.card ((Σ j : J,Fin (pads+1)) ⊕ (Σ j : J,Fin (s.2.2.1.1 j : ℕ))) ≤ _
  simp only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin,Finset.sum_const,
    Finset.card_univ,smul_eq_mul]
  exact Nat.add_le_add_left s.2.2.1.2 _

theorem markedMemoryHistoryBirths_card_le {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    Fintype.card (MarkedMemoryHistoryBirths hZ history) ≤ (n+1)*B+n*Fintype.card J := by
  induction n generalizing s with
  | zero =>
    change Fintype.card (MarkedMemoryGhostBirthIndex history) ≤ (0+1)*B+0*Fintype.card J
    simpa only [Nat.zero_add,Nat.one_mul,Nat.zero_mul,Nat.add_zero] using
      markedMemoryGhostBirthIndex_card_le hZ history
  | succ n ih =>
    change Fintype.card (MarkedMemoryGhostBirthIndex history.1 ⊕
      (MarkedMemoryEdgeBirthIndex history.2.1 ⊕ MarkedMemoryHistoryBirths hZ history.2.2)) ≤ _
    rw [Fintype.card_sum,Fintype.card_sum]
    have hg := markedMemoryGhostBirthIndex_card_le hZ history.1
    have he := markedMemoryEdgeBirthIndex_card_le hZ history.2.1
    have ht := ih history.2.2
    simp only [Nat.add_mul,Nat.one_mul] at ht ⊢
    omega

variable [DecidableEq J]

omit [DecidableEq J] in
theorem markedMemoryHistoryTraceAddress_card_le {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    Fintype.card (MarkedMemoryHistoryTraceAddress hZ history) ≤
      Fintype.card J*(pads+1)+B+(n+1)*B+n*Fintype.card J := by
  rw [Fintype.card_congr (markedMemoryHistoryFiniteTraceEquiv hZ history),Fintype.card_sum]
  have hp := markedMemoryPopulationIndex_card_le s
  have hb := markedMemoryHistoryBirths_card_le hZ history
  omega

theorem markedMemoryActualFiber_card_le {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (j : J) :
    Fintype.card (MarkedMemoryActualFiber hZ history j) ≤
      Fintype.card J*(pads+1)+B+(n+1)*B+n*Fintype.card J :=
  (Fintype.card_subtype_le _).trans (markedMemoryHistoryTraceAddress_card_le hZ history)

end
end ArtinMatthews
