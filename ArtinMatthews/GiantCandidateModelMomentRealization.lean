module

public import ArtinMatthews.GiantCandidateCountMoments
public import ArtinMatthews.GiantCandidateBoxBinomialMoment
public import ArtinMatthews.GiantCandidateFullResidueModel
public import ArtinMatthews.GiantCandidateFullModelSelection
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

/-! Realize the selected-prime model moments as ordinary expectations
on the full independent residue carrier. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateActualHitCounts {ι : Type*} [Fintype ι] {j : ℕ}
    (G : ι → Finset ℕ) (side : ι → GiantCandidateHitSide) (t : Fin j → ℕ) (i : ι) : ℕ :=
  (giantCandidateHitSet (G i) (side i) (∏ v,t v)).card

def giantCandidateModelHitCounts {ι : Type*} [Fintype ι] {j : ℕ}
    (G : ι → Finset ℕ) (side : ι → GiantCandidateHitSide)
    (t : GiantCandidateModelResidueSpace G j) (i : ι) : ℕ :=
  (giantCandidateModelHitSet G side t i).card

theorem giantCandidateActualHitCounts_moment_eq {ι : Type*} [Fintype ι] {j : ℕ}
    (S : Fin j → Finset ℕ) (G : ι → Finset ℕ) (side : ι → GiantCandidateHitSide) (k : ι → ℕ) :
    giantCandidateCountMoment (Fintype.piFinset S) (giantCandidateActualHitCounts G side) k =
      giantCandidateBoxBinomialMoment S G side k := by
  unfold giantCandidateCountMoment
  rw [expect_eq_sum_div_card]
  rfl

private theorem giantCandidateBinomialProduct_eq_subsets {ι : Type*} [Fintype ι]
    (G H : ι → Finset ℕ) (k : ι → ℕ) (hH : ∀ i,H i⊆G i) :
    (∏ i,((H i).card.choose (k i):ℝ)) =
      ∑ D∈giantCandidateHitSelections G k,if ∀i,D i⊆H i then (1:ℝ) else 0 := by
  classical
  have he : (giantCandidateHitSelections G k).filter (fun D => ∀i,D i⊆H i) =
      Fintype.piFinset (fun i => (H i).powersetCard (k i)) := by
    ext D
    simp only [mem_filter,mem_giantCandidateHitSelections,Fintype.mem_piFinset,mem_powersetCard]
    constructor
    · rintro ⟨hg,hh⟩ i
      exact ⟨hh i,(hg i).2⟩
    · intro hh
      exact ⟨fun i => ⟨(hh i).1.trans (hH i),(hh i).2⟩,fun i => (hh i).1⟩
  symm
  rw [← sum_filter,sum_const,nsmul_eq_mul,mul_one,he,Fintype.card_piFinset,Nat.cast_prod]
  simp only [card_powersetCard]

theorem giantCandidateModelHitCounts_moment_eq {ι : Type*} [Fintype ι] (j : ℕ)
    (G : ι → Finset ℕ) (side : ι → GiantCandidateHitSide) (k : ι → ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) :
    giantCandidateCountMoment (giantCandidateModelResidueTuples G hG j)
      (giantCandidateModelHitCounts G side) k = giantCandidateModelBinomialMoment j G side k hG := by
  classical
  let T := giantCandidateModelResidueTuples G hG j
  let E := giantCandidateHitSelections G k
  let F (D : ι → Finset ℕ) (t : GiantCandidateModelResidueSpace G j) :=
    ∀i,D i⊆giantCandidateModelHitSet G side t i
  have hrow (t : GiantCandidateModelResidueSpace G j) :
      giantCandidateCountBinomialTest k (giantCandidateModelHitCounts G side t) =
        ∑ D∈E,if F D t then (1:ℝ) else 0 :=
    giantCandidateBinomialProduct_eq_subsets G (giantCandidateModelHitSet G side t) k
      (giantCandidateModelHitSet_subset G side t)
  unfold giantCandidateCountMoment giantCandidateModelBinomialMoment
  rw [expect_eq_sum_div_card]
  simp_rw [hrow]
  rw [sum_comm,sum_div,← sum_coe_sort]
  apply sum_congr rfl
  intro D _
  rw [← sum_filter,sum_const,nsmul_eq_mul,mul_one]
  exact giantCandidateModelSelection_mass G side k hG j D

end
end ArtinMatthews
