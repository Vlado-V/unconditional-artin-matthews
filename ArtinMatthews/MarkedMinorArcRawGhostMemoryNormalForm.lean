module

public import ArtinMatthews.MarkedMinorArcRawGhostChargeRule
public import ArtinMatthews.MarkedMinorArcRawGhostDegreeEligibility
public import ArtinMatthews.MarkedMinorArcRawGhostDegreeAdjoint
public import ArtinMatthews.MarkedMinorArcRawGhostDegreeTransport
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
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact degree normal form of the literal total-truncated ghost action.
This identifies its actual indexed choices and measure with the grouped
factorial components, rather than assuming a memory transition identity. -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem markedRawGhost_degree_charge_coefficient {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (δ γ s : J → ℝ) {B : ℕ}
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (a : MarkedRawGhostDegreeShape J B)
    (data : MarkedRawGhostDegreePayload P z hz a) :
    let c := markedRawGhostDegreeMemoryChoice P z hz a data
    markedRawGhostChargeCoefficient δ γ s c.1 z hz c.2.1.1 c.2.2.1=
      ∏ j,δ j^(a.1.deleted j)*
        s j^(markedRawTupleHitCount (P j) z hz
          (markedRawSurvivorTupleCast (a.2 j).1 (markedRawDeletionBatch_survivor_card rfl (a.2 j)) (data.1.1 j)))*
        γ j^(a.1.born j) := by
  unfold markedRawGhostChargeCoefficient
  apply Finset.prod_congr rfl
  intro j _
  have hh := markedRawGhost_survivor_tuple_hits
    (markedRawGhostDegreeMemoryChoice P z hz a data).1 z hz
    (markedRawGhostDegreeMemoryChoice P z hz a data).2.1.1 j
    (markedRawDeletionBatch_survivor_card rfl (a.2 j))
  change δ j^((a.2 j).1.card)*
    s j^((markedRawGroupHitIndices (markedRawGhostDegreeMemoryChoice P z hz a data).1 j z hz \ (a.2 j).1).card)*
      γ j^(a.1.born j)=_
  erw [markedRawDeletionBatch_deleted_card,← hh]
  rfl

theorem markedRawGhost_degree_hit_product {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B)
    (old : (j : J) → Fin (a.1.survivors j+a.1.deleted j) → MarkedRawParticle (P j)) :
    (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz
      (markedRawDeletedTupleCast (a.2 j).1 (markedRawDeletionBatch_deleted_card (a.2 j)) (old j) i)
        then (1:ℂ) else 0)=
      if MarkedRawGhostDegreeAllowed P z hz a old then 1 else 0 := by
  classical
  by_cases h : MarkedRawGhostDegreeAllowed P z hz a old
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro j _
    apply Finset.prod_eq_one
    intro i _
    exact ite_eq_left ((markedRawGhostDegreeAllowed_iff P z hz a old).mp h j i)
  · rw [ite_eq_right h]
    have hn : ¬∀ j i,MarkedRawParticleHits (P j) z hz
        (markedRawDeletedTupleCast (a.2 j).1 (markedRawDeletionBatch_deleted_card (a.2 j)) (old j) i) :=
      fun hh => h ((markedRawGhostDegreeAllowed_iff P z hz a old).mpr hh)
    obtain ⟨j,hj⟩ := not_forall.mp hn
    obtain ⟨i,hi⟩ := not_forall.mp hj
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi))

noncomputable def markedRawGhostMemoryChoicePairing {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ s : J → ℝ)
    {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (f g : MarkedRawMemory P B → ℂ) (c : MarkedRawGhostMemoryChoice P B z hz) : ℂ :=
  (markedRawMemoryMass ν c.1 : ℂ)*g c.1*
    ((markedRawGhostChargeCoefficient δ γ s c.1 z hz c.2.1.1 c.2.2.1*
      markedRawGhostBirthMass ν c.2.2.1 c.2.2.2 : ℝ) : ℂ)*
      f (markedRawGhostTargetMemory c.1 z hz c.2.1.1 c.2.2.1 c.2.2.2)

theorem markedRawGhostMemoryRule_pairing_choices {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ s : J → ℝ)
    {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (f g : MarkedRawMemory P B → ℂ) :
    (∑ m : MarkedRawMemory P B,(markedRawMemoryMass ν m : ℂ)*g m*
      markedRawGhostMemoryRule ν δ γ s z hz f m)=
      ∑ m : MarkedRawMemory P B,
        ∑ del : {d : MarkedRawGhostDeletion m // MarkedRawGhostDeletionAllowed m z hz d},
          ∑ l : MarkedRawGhostBirthSizes m del.1, ∑ births : MarkedRawGhostBirthLabels l,
            markedRawGhostMemoryChoicePairing ν δ γ s z hz f g ⟨m,del,l,births⟩ := by
  classical
  apply Finset.sum_congr rfl
  intro m _
  have hExpand : (markedRawMemoryMass ν m : ℂ)*g m*markedRawGhostMemoryRule ν δ γ s z hz f m=
      ∑ del : MarkedRawGhostDeletion m,
        if h : MarkedRawGhostDeletionAllowed m z hz del then
          ∑ l : MarkedRawGhostBirthSizes m del, ∑ births : MarkedRawGhostBirthLabels l,
            markedRawGhostMemoryChoicePairing ν δ γ s z hz f g ⟨m,⟨del,h⟩,l,births⟩ else 0 := by
    unfold markedRawGhostMemoryRule
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro del _
    split_ifs
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro births _
      unfold markedRawGhostMemoryChoicePairing
      ring
    · exact mul_zero _
  rw [hExpand]
  have hh := Finset.sum_dite (s := Finset.univ)
    (fun del h => ∑ l : MarkedRawGhostBirthSizes m del, ∑ births : MarkedRawGhostBirthLabels l,
      markedRawGhostMemoryChoicePairing ν δ γ s z hz f g ⟨m,⟨del,h⟩,l,births⟩)
    (fun _ _ => (0:ℂ))
  erw [hh]
  simp only [Finset.sum_const_zero,add_zero]
  exact (Equiv.subtypeEquivRight (by simp)).sum_comp
    (fun del : {d : MarkedRawGhostDeletion m // MarkedRawGhostDeletionAllowed m z hz d} =>
      ∑ l : MarkedRawGhostBirthSizes m del.1,∑ births : MarkedRawGhostBirthLabels l,
        markedRawGhostMemoryChoicePairing ν δ γ s z hz f g ⟨m,del,l,births⟩)

end ArtinMatthews
