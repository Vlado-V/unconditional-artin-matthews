module

public import ArtinMatthews.GiantCandidateCountVectorPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact-count indicators on a count vector are controlled by a
finite even polynomial and mixed first-omitted terms. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giantCandidateCountVectorPoly_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ℕ) (b : ℕ) (n : ι → ℕ) :
    let r := 2*b+1
    giantCandidateCountVectorDelta k n ≤ giantCandidateCountVectorPoly k b n ∧
      giantCandidateCountVectorPoly k b n ≤ giantCandidateCountVectorDelta k n+
        ∑ A∈giantCandidateCountErrorSubsets ι,giantCandidateCountErrorCoeff k r A*
          giantCandidateCountBinomialTest (giantCandidateCountErrorOrders k r A) n := by
  let r := 2*b+1
  let d (i : ι) := giantCandidatePointCountDelta (k i) (n i)
  let p (i : ι) := giantCandidatePointCountPoly (k i) (2*b) (n i)
  let e (i : ι) := ((k i+r).choose (k i):ℝ)*((n i).choose (k i+r):ℝ)
  let U := (univ : Finset ι)
  let F (A : Finset ι) := (∏ i∈A,e i)*(∏ i∈U \ A,d i)
  have hd₀ (i : ι) : 0≤d i := giantCandidatePointCountDelta_nonneg (k i) (n i)
  have hd₁ (i : ι) : d i≤1 := giantCandidatePointCountDelta_le_one (k i) (n i)
  have hde (i : ι) : d i≤p i ∧ p i≤d i+e i :=
    giantCandidatePointCountPoly_bounds (k i) b (n i)
  have he₀ (i : ι) : 0≤e i := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hδ : giantCandidateCountVectorDelta k n = ∏ i,d i := giantCandidateCountVectorDelta_eq_prod k n
  change giantCandidateCountVectorDelta k n≤(∏ i,p i) ∧
    (∏ i,p i)≤giantCandidateCountVectorDelta k n+
      ∑ A∈giantCandidateCountErrorSubsets ι,giantCandidateCountErrorCoeff k r A*
        giantCandidateCountBinomialTest (giantCandidateCountErrorOrders k r A) n
  constructor
  · rw [hδ]
    exact prod_le_prod₀ (fun i _ => hd₀ i) (fun i _ => (hde i).1)
  · have hmem : (∅ : Finset ι)∈U.powerset := mem_powerset.mpr (empty_subset _)
    have hF₀ : F ∅=giantCandidateCountVectorDelta k n := by
      rw [hδ]
      simp only [F,prod_empty,sdiff_empty,one_mul,U]
    calc
      _ ≤ ∏ i,(e i+d i) := by
        apply prod_le_prod₀ (fun i _ => (hd₀ i).trans (hde i).1)
        intro i _
        exact (hde i).2.trans_eq (add_comm _ _)
      _ = ∑ A∈U.powerset,F A := prod_add e d U
      _ = F ∅+∑ A∈giantCandidateCountErrorSubsets ι,F A :=
        (add_sum_erase U.powerset F hmem).symm
      _ ≤ _ := by
        rw [hF₀]
        apply add_le_add_right
        apply sum_le_sum
        intro A _
        have hdA : (∏ i∈U \ A,d i)≤1 := by
          calc
            _ ≤ ∏ _i∈U \ A,(1:ℝ) := prod_le_prod₀ (fun i _ => hd₀ i) (fun i _ => hd₁ i)
            _ = _ := prod_const_one
        calc
          F A ≤ ∏ i∈A,e i :=
            mul_le_of_le_one_right (prod_nonneg (fun i _ => he₀ i)) hdA
          _ = _ := giantCandidateCountErrorTerm_eq k n r A

end
end ArtinMatthews
