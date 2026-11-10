module

public import ArtinMatthews.MarkedMinorArcRawEdgeSlotIntegral
public import Mathlib.CategoryTheory.Category.Basic
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

/-! The coupled store/promote factorial transpose at fixed degrees.  Both
old and new pending lists remain arguments of the kernel, so geometric
cutoffs, endpoint projections and test functions can stay inside it. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- One literal fixed-degree edge component.  Deletions are actual old
index subsets, stored particles use the source active labels and source
anchors, and promoted particles fill the target active labels. -/
def markedRawEdgeSlotComponent
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    (x y : ℤ × ℤ) (hx : IsCoprime x.1 x.2) (hy : IsCoprime y.1 y.2)
    (n d l : J → ℕ) (δ γ : J → ℂ)
    (a : (j : J) → ↥(P j))
    (K : ((j : J) → Fin (n j + d j) → MarkedRawParticle (P j)) →
      ((j : J) → ↥(P j)) →
      ((j : J) → Fin (n j + l j) → MarkedRawParticle (P j)) → ℂ)
    (old : (j : J) → Fin (n j + d j) → MarkedRawParticle (P j)) : ℂ := by
  classical
  exact (∏ j, δ j ^ d j * γ j ^ l j) *
    ∑ S : (j : J) → MarkedRawDeletionBatch (n j + d j) (d j),
      (∏ j, ∏ i, if MarkedRawParticleHits (P j) y hy
        (markedRawDeletedTupleCast (S j).1
          (markedRawDeletionBatch_deleted_card (S j)) (old j) i)
          then (1 : ℂ) else 0) *
        ∑ b : (j : J) → ↥(P j), markedRawEdgeFreePrimeMass ν d b *
          (if MarkedRawEdgeRetrievedSlots
            (fun j i => (markedRawDeletedTupleCast (S j).1
              (markedRawDeletionBatch_deleted_card (S j)) (old j) i).1) b
            then (1 : ℂ) else 0) *
          K old b (fun j => Fin.addCases
            (markedRawSurvivorTupleCast (S j).1
              (markedRawDeletionBatch_survivor_card rfl (S j)) (old j))
            (markedRawAnchoredBatch (P j) x hx (l j) (fun _ => a j)))

/-- Exact canonical survivor integral of the literal selected-index edge.
No factorization of the coupled old/new endpoint kernel is required. -/
theorem markedRawEdge_slot_component_pairing
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    (x y : ℤ × ℤ) (hx : IsCoprime x.1 x.2) (hy : IsCoprime y.1 y.2)
    (n d l : J → ℕ) (hd : ∀ j, d j ≤ 1) (δ γ : J → ℂ)
    (a : (j : J) → ↥(P j))
    (K : ((j : J) → Fin (n j + d j) → MarkedRawParticle (P j)) →
      ((j : J) → ↥(P j)) →
      ((j : J) → Fin (n j + l j) → MarkedRawParticle (P j)) → ℂ)
    (hK : ∀ b new, MarkedRawGroupedTupleSymmetric (fun j => n j + d j)
      (fun old => K old b new)) :
    (∑ old : (j : J) → Fin (n j + d j) → MarkedRawParticle (P j),
      ((∏ j, ∏ i, ν j (old j i).1) /
        (∏ j, (Nat.factorial (n j + d j) : ℂ))) *
        markedRawEdgeSlotComponent P ν x y hx hy n d l δ γ a K old) =
      (∏ j, δ j ^ d j * γ j ^ l j) *
        ∑ survivors : (j : J) → Fin (n j) → MarkedRawParticle (P j),
          ((∏ j, ∏ i, ν j (survivors j i).1) /
            (∏ j, (Nat.factorial (n j) : ℂ))) *
            ∑ b : (j : J) → ↥(P j), (∏ j, ν j (b j)) *
              K (fun j => Fin.addCases (survivors j)
                (markedRawAnchoredBatch (P j) y hy (d j) (fun _ => b j))) b
                (fun j => Fin.addCases (survivors j)
                  (markedRawAnchoredBatch (P j) x hx (l j) (fun _ => a j))) := by
  classical
  unfold markedRawEdgeSlotComponent
  simp_rw [mul_left_comm _ (∏ j, δ j ^ d j * γ j ^ l j)]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [Fin.cast_eq_self] using markedRawEdge_slot_integral P ν y hy
    (fun _ => rfl) hd
    (fun old b survivors => K old b (fun j => Fin.addCases (survivors j)
      (markedRawAnchoredBatch (P j) x hx (l j) (fun _ => a j))))
    (fun b survivors => hK b _)

/-- The full coupled fixed-degree transpose swaps promoted and stored
flags and their charges.  The prime atoms can vanish: no division by an
atom, positivity assumption or adjoint hypothesis is used. -/
theorem markedRawEdge_slot_component_transpose
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    (x y : ℤ × ℤ) (hx : IsCoprime x.1 x.2) (hy : IsCoprime y.1 y.2)
    (n d l : J → ℕ) (hd : ∀ j, d j ≤ 1) (hl : ∀ j, l j ≤ 1) (δ γ : J → ℂ)
    (K : ((j : J) → ↥(P j)) →
      ((j : J) → Fin (n j + d j) → MarkedRawParticle (P j)) →
      ((j : J) → ↥(P j)) →
      ((j : J) → Fin (n j + l j) → MarkedRawParticle (P j)) → ℂ)
    (hKold : ∀ a b new, MarkedRawGroupedTupleSymmetric (fun j => n j + d j)
      (fun old => K a old b new))
    (hKnew : ∀ a old b, MarkedRawGroupedTupleSymmetric (fun j => n j + l j)
      (fun new => K a old b new)) :
    (∑ a : (j : J) → ↥(P j), (∏ j, ν j (a j)) *
      ∑ old : (j : J) → Fin (n j + d j) → MarkedRawParticle (P j),
        ((∏ j, ∏ i, ν j (old j i).1) /
          (∏ j, (Nat.factorial (n j + d j) : ℂ))) *
          markedRawEdgeSlotComponent P ν x y hx hy n d l δ γ a (K a) old) =
      ∑ b : (j : J) → ↥(P j), (∏ j, ν j (b j)) *
        ∑ new : (j : J) → Fin (n j + l j) → MarkedRawParticle (P j),
          ((∏ j, ∏ i, ν j (new j i).1) /
            (∏ j, (Nat.factorial (n j + l j) : ℂ))) *
            markedRawEdgeSlotComponent P ν y x hy hx n l d γ δ b
              (fun new a old => K a old b new) new := by
  classical
  simp_rw [markedRawEdge_slot_component_pairing P ν x y hx hy n d l hd δ γ _ _
    (hKold _)]
  simp_rw [markedRawEdge_slot_component_pairing P ν y x hy hx n l d hl γ δ _ _
    (fun a old => hKnew a old _)]
  have hcharge : (∏ j, γ j ^ l j * δ j ^ d j) = ∏ j, δ j ^ d j * γ j ^ l j :=
    Finset.prod_congr rfl (fun j _ => mul_comm _ _)
  rw [hcharge]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro survivors _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

end
end ArtinMatthews
