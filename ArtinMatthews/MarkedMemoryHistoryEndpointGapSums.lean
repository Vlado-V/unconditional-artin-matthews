module

public import ArtinMatthews.MarkedMemoryLifespanInternalGaps
public import ArtinMatthews.MarkedMemoryHistoryEndpointSums
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

/-! The finite optional endpoint sums, decomposed into the actual
consecutive active gaps, give the existing prefix/internal/suffix factors.
The statements are scalar identities and assert no history coverage. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedMemoryPrefixChoice_sum_lines {N : ℕ} {Λ : Type*} [DecidableEq Λ]
    (η : Fin (N+1) → ℝ) (line : Fin (N+1) → Λ) (a : Fin (N+1)) :
    (∑ choice : MarkedMemoryPrefixChoice a,
      markedMemoryPrefixChoiceScalar (fun v => η v*markedLineHit line v (line a)) a choice) =
      markedMemoryPrefixGhost η line a := by
  rw [markedMemoryPrefixChoiceScalar_sum]
  exact markedMemoryPrefixGhost_eq η line a

theorem markedMemorySuffixChoice_sum_lines {N : ℕ} {Λ : Type*} [DecidableEq Λ]
    (η : Fin (N+1) → ℝ) (line : Fin (N+1) → Λ) (a c : Fin (N+1)) :
    (∑ choice : MarkedMemorySuffixChoice c,
      markedMemorySuffixChoiceScalar (fun v => η v*markedLineHit line v (line a)) c choice) =
      markedMemorySuffixGhost η line a c := by
  rw [markedMemorySuffixChoiceScalar_sum]
  exact markedMemorySuffixGhost_eq η line a c

theorem markedMemoryActiveEndpoint_sum_lines {N : ℕ} {Λ : Type*} [DecidableEq Λ]
    (A : Finset (Fin (N+1))) (hA : A.Nonempty) (η : Fin (N+1) → ℝ) (line : Fin (N+1) → Λ) :
    (∑ choice : MarkedMemoryActiveEndpointChoice A hA,
      markedMemoryActiveEndpointScalar A hA
        (fun v => η v*markedLineHit line v (line (A.min' hA))) choice) =
      markedMemoryPrefixGhost η line (A.min' hA) *
        markedMemoryInternalDamping A η line (A.min' hA) (A.max' hA) *
        markedMemorySuffixGhost η line (A.min' hA) (A.max' hA) := by
  rw [markedMemoryActiveEndpoint_sum,
    markedMemory_inactive_product A hA (fun v => 1-η v*markedLineHit line v (line (A.min' hA))),
    markedMemoryPrefixGhost_eq, markedMemorySuffixGhost_eq]
  rfl

def markedMemoryGapEndpointScalar {N : ℕ} (A : Finset (Fin (N+1))) (hA : A.Nonempty)
    (u : Fin (N+1) → ℝ) (choice : MarkedMemoryActiveEndpointChoice A hA) : ℝ :=
  markedMemoryPrefixChoiceScalar u (A.min' hA) choice.1 *
    (∏ gap : MarkedMemoryActiveGap A, ∏ v ∈ markedMemoryGapVertices gap, (1-u v)) *
    markedMemorySuffixChoiceScalar u (A.max' hA) choice.2

theorem markedMemoryGapEndpointScalar_eq {N : ℕ} (A : Finset (Fin (N+1))) (hA : A.Nonempty)
    (u : Fin (N+1) → ℝ) (choice : MarkedMemoryActiveEndpointChoice A hA) :
    markedMemoryGapEndpointScalar A hA u choice = markedMemoryActiveEndpointScalar A hA u choice := by
  unfold markedMemoryGapEndpointScalar markedMemoryActiveEndpointScalar
  rw [← markedMemoryInternal_product_gaps A hA]

theorem markedMemoryGapEndpoint_sum {N : ℕ} (A : Finset (Fin (N+1))) (hA : A.Nonempty)
    (u : Fin (N+1) → ℝ) :
    (∑ choice : MarkedMemoryActiveEndpointChoice A hA, markedMemoryGapEndpointScalar A hA u choice) =
      ∏ v ∈ Finset.univ \ A, (1-u v) := by
  simp_rw [markedMemoryGapEndpointScalar_eq]
  exact markedMemoryActiveEndpoint_sum A hA u

/-- The internal products retain the actual source q at each hitting
vertex and one at each nonhit, including endpoint square roots. -/
theorem markedMemoryGapDamping_source {N : ℕ} {Λ : Type*} [DecidableEq Λ]
    (A : Finset (Fin (N+1))) (hA : A.Nonempty) (q : ℝ) (line : Fin (N+1) → Λ) :
    markedMemoryInternalDamping A (markedMemoryEta q N) line (A.min' hA) (A.max' hA) =
      ∏ gap : MarkedMemoryActiveGap A, ∏ v ∈ markedMemoryGapVertices gap,
        if line v = line (A.min' hA) then markedMemoryVisitQ q N v else 1 := by
  unfold markedMemoryInternalDamping
  rw [markedMemoryInternal_product_gaps A hA]
  apply Finset.prod_congr rfl
  intro gap _
  apply Finset.prod_congr rfl
  intro v _
  exact markedMemory_damping_hit_iff q line (A.min' hA) v

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryHistoryIndexedProjectiveFactor_gap_endpoint_sum
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (a : MarkedMemoryHistoryTraceAddress hZ history)
    (hA : (markedMemoryHistoryScalarActiveVisits hZ history a).Nonempty) (q : ℝ) :
    markedMemoryHistoryIndexedProjectiveFactor hZ history q a =
      (1 / ((markedMemoryHistoryTraceAddressPrime hZ history a : ℝ)+1)) *
        ∑ choice : MarkedMemoryActiveEndpointChoice (markedMemoryHistoryScalarActiveVisits hZ history a) hA,
          markedMemoryGapEndpointScalar (markedMemoryHistoryScalarActiveVisits hZ history a) hA
            (markedMemoryHistoryScalarVertexAtom hZ history q a) choice := by
  simp_rw [markedMemoryGapEndpointScalar_eq]
  exact markedMemoryHistoryIndexedProjectiveFactor_endpoint_sum hZ history ha a hA q

end
end ArtinMatthews
