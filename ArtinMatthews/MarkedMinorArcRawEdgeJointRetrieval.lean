module

public import ArtinMatthews.MarkedMinorArcRawMemoryAnchors
public import ArtinMatthews.MarkedMinorArcRawMemoryBulkFactorial
public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedSubset
public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedAnchors
public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedJoint
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact anchored retrieval integration for a joint edge kernel.  The
kernel may couple the old memory, retrieved prime labels and surviving
memory; all physical joint endpoint restrictions may therefore remain
inside it. -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRawEdge_joint_retrieval_pairing
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) {k n d : J → ℕ}
    (hk : ∀ j,n j+d j=k j)
    (H : ((j : J) → Fin (k j) → MarkedRawParticle (P j)) →
      ((j : J) → Fin (d j) → ↥(P j)) →
      ((j : J) → Fin (n j) → MarkedRawParticle (P j)) → ℂ)
    (hH : ∀ retrieved survivors,MarkedRawGroupedTupleSymmetric k
      (fun old => H old retrieved survivors)) :
    (∑ old : (j : J) → Fin (k j) → MarkedRawParticle (P j),
      ((∏ j,∏ i,ν j (old j i).1)/(∏ j,(Nat.factorial (k j) : ℂ)))*
        ∑ S : (j : J) → MarkedRawDeletionBatch (k j) (d j),
          (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz
            (markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (old j) i)
              then (1:ℂ) else 0)*
            H old (fun j i => (markedRawDeletedTupleCast (S j).1
              (markedRawDeletionBatch_deleted_card (S j)) (old j) i).1)
              (fun j => markedRawSurvivorTupleCast (S j).1
                (markedRawDeletionBatch_survivor_card (hk j) (S j)) (old j)))=
      ∑ survivors : (j : J) → Fin (n j) → MarkedRawParticle (P j),
        ((∏ j,∏ i,ν j (survivors j i).1)/(∏ j,(Nat.factorial (n j) : ℂ)))*
          ∑ retrieved : (j : J) → Fin (d j) → ↥(P j),
            ((∏ j,∏ i,ν j (retrieved j i))/(∏ j,(Nat.factorial (d j) : ℂ)))*
              H (fun j i => Fin.addCases (survivors j)
                (markedRawAnchoredBatch (P j) z hz (d j) (retrieved j)) (Fin.cast (hk j).symm i))
                retrieved survivors := by
  classical
  have hn : (∏ j,(Nat.factorial (n j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hd : (∏ j,(Nat.factorial (d j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have h := markedRawMemory_grouped_joint_factorial hk
    (fun j (a : MarkedRawParticle (P j)) => ν j a.1)
    (fun old deleted survivors =>
      (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz (deleted j i) then (1:ℂ) else 0)*
        H old (fun j i => (deleted j i).1) survivors)
    (by
      intro deleted survivors old σ
      dsimp only
      congr 1
      exact hH _ _ old σ)
  rw [h,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro survivors _
  calc
    _ = ((∏ j,∏ i,ν j (survivors j i).1)/(∏ j,(Nat.factorial (n j) : ℂ)))*
        ((∑ deleted : (j : J) → Fin (d j) → MarkedRawParticle (P j),
          (∏ j,∏ i,ν j (deleted j i).1)*
            (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz (deleted j i) then (1:ℂ) else 0)*
            H (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i))
              (fun j i => (deleted j i).1) survivors)/(∏ j,(Nat.factorial (d j) : ℂ))) := by
      rw [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro deleted _
      field_simp
    _ = _ := by
      rw [markedRawParticle_grouped_batch_hit_integral P ν z hz d
        (fun deleted => H (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i))
          (fun j i => (deleted j i).1) survivors)]
      simp only [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro retrieved _
      have hprime : (fun j i => (markedRawAnchoredBatch (P j) z hz (d j) (retrieved j) i).1)=retrieved := rfl
      rw [hprime]
      ring

end ArtinMatthews
