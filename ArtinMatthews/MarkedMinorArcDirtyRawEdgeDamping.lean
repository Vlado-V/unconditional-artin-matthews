module

public import ArtinMatthews.MarkedMinorArcDirtyPromotionChoices
public import ArtinMatthews.MarkedMinorArcRawEdgeState
public import ArtinMatthews.MarkedMinorArcRawGhostHits
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

/-! Actual outgoing edge memory damping. Stores are anchored at the source;
their target hits are only counted as nonnegative extra hits. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedDirtyGhostTargetMemory_surviving_hits_le {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (source target : ℤ × ℤ) (hsource : IsCoprime source.1 source.2) (htarget : IsCoprime target.1 target.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del)
    (births : MarkedRawGhostBirthLabels l) (j : J) :
    (markedRawGroupHitIndices m j target htarget \ del j).card ≤
      (markedRawGroupHitIndices (markedRawGhostTargetMemory m source hsource del l births) j target htarget).card := by
  classical
  have hcard : (markedRawGroupHitIndices (markedRawGhostTargetMemory m source hsource del l births) j target htarget).card=
      ∑ k, if MarkedRawParticleHits (P j) target htarget
        ((markedRawGhostTargetMemory m source hsource del l births).2 j k) then (1:ℕ) else 0 := by
    unfold markedRawGroupHitIndices
    simp only [Finset.sum_boole,Nat.cast_id]
  rw [hcard]
  change _ ≤ ∑ k : Fin ((markedRawGhostSurvivors m del j).card+(l.1 j:ℕ)),
    if MarkedRawParticleHits (P j) target htarget (Fin.addCases
      (fun k => m.2 j ((markedRawGhostSurvivors m del j).orderEmbOfFin rfl k))
      (fun k => markedRawAnchoredParticle (P j) (births j k) source hsource) k) then (1:ℕ) else 0
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right]
  rw [markedRawGhost_survivor_hit_count]
  exact Nat.le_add_right _ _

theorem markedDirtyRawEdge_remaining_group_hits_le {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (j : J) (k : Fin (s.2.2.1.1 j:ℕ))
    (hk : choice.promotions j=some k) :
    (markedRawPromotionRemainingHits s.2.2 j choice.target.1 (hZ _ choice.target.2) k).card ≤
      (markedRawGroupHitIndices (markedRawEdgeTargetMemory hZ s choice) j choice.target.1 (hZ _ choice.target.2)).card := by
  have hh := markedDirtyGhostTargetMemory_surviving_hits_le s.2.2 s.1.1 choice.target.1
    (hZ _ s.1.2) (hZ _ choice.target.2) (markedRawEdgePromotionDeletion choice.promotions)
    (markedRawEdgeStoreSizes hZ s choice) (fun j _ => ((markedRawActiveSplit pads) s.2.1).2 j) j
  simpa only [markedRawEdgePromotionDeletion,hk,Option.toFinset_some,
    Finset.sdiff_singleton_eq_erase,markedRawPromotionRemainingHits,markedRawEdgeTargetMemory] using hh

/-- The actual total outgoing damping is at most the product of the
retained old-hit damping in any selected promoted groups. -/
theorem markedDirtyRawEdge_outgoing_damping_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) (I : Finset J)
    (indices : MarkedRawPromotionTuple s.2.2 I)
    (hindices : ∀ j : I, choice.promotions j.1=some (indices j))
    {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    ρ^(markedRawPendingHits (markedRawEdgeTargetMemory hZ s choice) choice.target.1 (hZ _ choice.target.2)) ≤
      ∏ j : I, ρ^((markedRawPromotionRemainingHits s.2.2 j.1 choice.target.1
        (hZ _ choice.target.2) (indices j)).card) := by
  classical
  have hs : (∑ j : I, (markedRawPromotionRemainingHits s.2.2 j.1 choice.target.1
      (hZ _ choice.target.2) (indices j)).card) ≤
      markedRawPendingHits (markedRawEdgeTargetMemory hZ s choice) choice.target.1 (hZ _ choice.target.2) := by
    rw [markedRawPendingHits_eq_sum_card]
    calc
      _ ≤ ∑ j : I, (markedRawGroupHitIndices (markedRawEdgeTargetMemory hZ s choice) j.1
          choice.target.1 (hZ _ choice.target.2)).card := Finset.sum_le_sum (fun j _ =>
        markedDirtyRawEdge_remaining_group_hits_le hZ s choice j.1 (indices j) (hindices j))
      _ = ∑ j ∈ I, (markedRawGroupHitIndices (markedRawEdgeTargetMemory hZ s choice) j
          choice.target.1 (hZ _ choice.target.2)).card := Finset.sum_coe_sort I (fun j =>
            (markedRawGroupHitIndices (markedRawEdgeTargetMemory hZ s choice) j
              choice.target.1 (hZ _ choice.target.2)).card)
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.prod_pow_eq_pow_sum]
  exact pow_le_pow_of_le_one hρ₀ hρ₁ hs

end ArtinMatthews
