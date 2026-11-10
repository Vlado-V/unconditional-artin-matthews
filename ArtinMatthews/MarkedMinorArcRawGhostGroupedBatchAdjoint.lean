module

public import ArtinMatthews.MarkedMinorArcRawMemoryAnchors
public import ArtinMatthews.MarkedMinorArcRawMemoryBulkFactorial
public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedSubset
public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedAnchors
public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedFactorial
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

/-! The true factorial ghost deletion/anchored-birth pairing for all prime
groups at once. Arbitrary coupled pending functions are allowed, subject
only to their actual independent old-index permutation symmetry. -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Actual simultaneous unordered deletion/anchored creation integration.
The factorial product is obtained from actual finite indexed choices. -/
theorem markedRawGhost_grouped_batch_delete_pairing
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) {k n d : J → ℕ}
    (hk : ∀ j,n j+d j=k j)
    (g : ((j : J) → Fin (k j) → MarkedRawParticle (P j)) → ℂ)
    (hg : MarkedRawGroupedTupleSymmetric k g)
    (f : ((j : J) → Fin (n j) → MarkedRawParticle (P j)) → ℂ) :
    (∑ a : (j : J) → Fin (k j) → MarkedRawParticle (P j),
      ((∏ j,∏ i,ν j (a j i).1)/(∏ j,(Nat.factorial (k j) : ℂ)))*g a*
        ∑ S : (j : J) → MarkedRawDeletionBatch (k j) (d j),
          (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz
            (markedRawDeletedTupleCast (S j).1 (markedRawDeletionBatch_deleted_card (S j)) (a j) i)
              then (1:ℂ) else 0)*
            f (fun j => markedRawSurvivorTupleCast (S j).1
              (markedRawDeletionBatch_survivor_card (hk j) (S j)) (a j)))=
      ∑ survivors : (j : J) → Fin (n j) → MarkedRawParticle (P j),
        ((∏ j,∏ i,ν j (survivors j i).1)/(∏ j,(Nat.factorial (n j) : ℂ)))*f survivors*
          ∑ births : (j : J) → Fin (d j) → ↥(P j),
            ((∏ j,∏ i,ν j (births j i))/(∏ j,(Nat.factorial (d j) : ℂ)))*
              g (fun j i => Fin.addCases (survivors j)
                (markedRawAnchoredBatch (P j) z hz (d j) (births j)) (Fin.cast (hk j).symm i)) := by
  classical
  have hn : (∏ j,(Nat.factorial (n j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hd : (∏ j,(Nat.factorial (d j) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have h := markedRawMemory_grouped_factorial_batch_delete hk
    (fun j (a : MarkedRawParticle (P j)) => ν j a.1) g hg
    (fun deleted survivors =>
      (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz (deleted j i) then (1:ℂ) else 0)*f survivors)
  rw [h,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro survivors _
  calc
    _ = ((∏ j,∏ i,ν j (survivors j i).1)/(∏ j,(Nat.factorial (n j) : ℂ)))*f survivors*
        ((∑ deleted : (j : J) → Fin (d j) → MarkedRawParticle (P j),
          (∏ j,∏ i,ν j (deleted j i).1)*
            (∏ j,∏ i,if MarkedRawParticleHits (P j) z hz (deleted j i) then (1:ℂ) else 0)*
            g (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i)))/
              (∏ j,(Nat.factorial (d j) : ℂ))) := by
      rw [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro deleted _
      field_simp
    _ = _ := by
      rw [markedRawParticle_grouped_batch_hit_integral P ν z hz d
        (fun deleted => g (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i)))]
      simp only [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro births _
      ring

end ArtinMatthews
