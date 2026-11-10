module

public import ArtinMatthews.MarkedMinorArcRawGhostDegreeTransport
public import ArtinMatthews.MarkedMinorArcRawGhostDegreeEligibility
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical target is literally the survivor-then-anchored-birth
memory at its target cutoff. The deleted-hit indicator is exact. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem markedRawGhostDegreeAllowed_indicator {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B)
    (old : (j : J) → Fin (a.1.survivors j+a.1.deleted j) → MarkedRawParticle (P j)) :
    (∏ j, ∏ i, if MarkedRawParticleHits (P j) z hz
      (markedRawDeletedTupleCast (a.2 j).1 (markedRawDeletionBatch_deleted_card (a.2 j)) (old j) i)
        then (1:ℂ) else 0)=
      if MarkedRawGhostDegreeAllowed P z hz a old then 1 else 0 := by
  classical
  by_cases h : MarkedRawGhostDegreeAllowed P z hz a old
  · have hh := (markedRawGhostDegreeAllowed_iff P z hz a old).mp h
    simp only [hh,ite_true,Finset.prod_const_one,h]
  · have hh := mt (markedRawGhostDegreeAllowed_iff P z hz a old).mpr h
    push Not at hh
    obtain ⟨j,i,hi⟩ := hh
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi))

theorem markedRawGhost_degree_target {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B) (data : MarkedRawGhostDegreePayload P z hz a) :
    let c := markedRawGhostDegreeMemoryChoice P z hz a data
    markedRawGhostTargetMemory c.1 z hz c.2.1.1 c.2.2.1 c.2.2.2 =
      markedRawMemoryOfDegrees P (fun j => a.1.survivors j+a.1.born j) a.1.target_le
        (markedRawGhostDegreeTargetTuple P z hz a data) := by
  exact markedRawMemory_eq_of_degrees _ _ _ _
    (markedRawGhost_degree_target_sizes P z hz a data)
    (markedRawGhost_degree_target_tuple P z hz a data)

end
end ArtinMatthews
