module

public import ArtinMatthews.GiantCandidateCountComparisonBudget
public import ArtinMatthews.GiantCandidateCountMeanCompare
public import ArtinMatthews.GiantCandidateCountMeanTail
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

/-! Any bounded test of a fixed finite count vector is determined
uniformly by a finite, fixed collection of its joint binomial moments. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

private theorem giantCandidateCountTruncatedMean_compare {ι Ω Ξ : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset Ω) (T : Finset Ξ) (N : Ω → ι → ℕ) (M : Ξ → ι → ℕ)
    {C : ℝ} (hC : 0≤C) (a b : ℕ) (hR : giantCandidateCountRemainderScale C a (2*b+1)≤1)
    (η : ℝ)
    (hS : ∀ l∈giantCandidateCountVectors ι (a+2*b+1),
      giantCandidateCountMoment S N l≤2*giantCandidateMomentEnvelope C l)
    (hT : ∀ l∈giantCandidateCountVectors ι (a+2*b+1),
      giantCandidateCountMoment T M l≤2*giantCandidateMomentEnvelope C l)
    (h : ∀ l∈giantCandidateCountVectors ι (a+2*b+1),
      |giantCandidateCountMoment S N l-giantCandidateCountMoment T M l|≤η)
    (f : (ι → ℕ) → ℝ) (hf : ∀ k,|f k|≤1) :
    |giantCandidateCountTruncatedMean S N a f-giantCandidateCountTruncatedMean T M a f|≤
      2*((giantCandidateCountVectors ι a).card:ℝ)*
        (2*(2:ℝ)^Fintype.card ι*giantCandidateCountRemainderScale C a (2*b+1))+
        giantCandidateCountPolyCost ι a b*η := by
  let E := giantCandidateCountVectors ι a
  let R := 2*(2:ℝ)^Fintype.card ι*giantCandidateCountRemainderScale C a (2*b+1)
  let A (k : ι → ℕ) := (𝔼 t∈S,giantCandidateCountVectorDelta k (N t))-
    (𝔼 t∈T,giantCandidateCountVectorDelta k (M t))
  let P (k : ι → ℕ) := ∑ l∈giantCandidateCountVectors ι (2*b),|giantCandidateCountPolyCoeff k l|
  unfold giantCandidateCountTruncatedMean
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  change |∑ k∈E,f k*A k|≤2*(E.card:ℝ)*R+giantCandidateCountPolyCost ι a b*η
  calc
    _ ≤ ∑ k∈E,|f k| * |A k| := by
      simp only [← abs_mul]
      exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ k∈E,(2*R+P k*η) := by
      apply sum_le_sum
      intro k hk
      exact (mul_le_of_le_one_left (abs_nonneg _) (hf k)).trans
        (giantCandidateCountDeltaMean_compare S T N M hC k
          (mem_giantCandidateCountVectors.mp hk) b hR η hS hT h)
    _ = _ := by
      rw [sum_add_distrib,sum_const,nsmul_eq_mul,← sum_mul]
      change (E.card:ℝ)*(2*R)+giantCandidateCountPolyCost ι a b*η=_
      ring

theorem giantCandidateBoundedCountTests_from_moments (ι : Type*) [Fintype ι] [DecidableEq ι]
    {C δ : ℝ} (hC : 0≤C) (hδ : 0<δ) :
    ∃ K : ℕ,∃ η : ℝ,0<η ∧
      ∀ {Ω Ξ : Type} (S : Finset Ω) (T : Finset Ξ) (N : Ω → ι → ℕ) (M : Ξ → ι → ℕ),
        (∀ k∈giantCandidateCountVectors ι K,
          giantCandidateCountMoment S N k≤2*giantCandidateMomentEnvelope C k) →
        (∀ k∈giantCandidateCountVectors ι K,
          giantCandidateCountMoment T M k≤2*giantCandidateMomentEnvelope C k) →
        (∀ k∈giantCandidateCountVectors ι K,
          |giantCandidateCountMoment S N k-giantCandidateCountMoment T M k|≤η) →
        ∀ f : (ι → ℕ) → ℝ,(∀ k,|f k|≤1) →
          |(𝔼 t∈S,f (N t))-(𝔼 t∈T,f (M t))|≤δ := by
  obtain ⟨a,b,η,hη,htail,hR,hpoint,hpoly⟩ := giantCandidateCountComparisonBudget ι (C:=C) hδ
  refine ⟨a+2*b+1,η,hη,?_⟩
  intro Ω Ξ S T N M hS hT h f hf
  have hu (i : ι) : (fun l => if l=i then 1 else 0)∈giantCandidateCountVectors ι (a+2*b+1) := by
    apply mem_giantCandidateCountVectors.mpr
    intro l
    split_ifs <;> omega
  have hfirstS (i : ι) : (𝔼 t∈S,(N t i:ℝ))≤2*C := by
    simpa only [giantCandidateCountMoment_one_coordinate,giantCandidateMomentEnvelope_one_coordinate] using
      hS _ (hu i)
  have hfirstT (i : ι) : (𝔼 t∈T,(M t i:ℝ))≤2*C := by
    simpa only [giantCandidateCountMoment_one_coordinate,giantCandidateMomentEnvelope_one_coordinate] using
      hT _ (hu i)
  let A := 𝔼 t∈S,f (N t)
  let B := 𝔼 t∈T,f (M t)
  let A' := giantCandidateCountTruncatedMean S N a f
  let B' := giantCandidateCountTruncatedMean T M a f
  have h₁ : |A-A'|≤δ/6 := (giantCandidateCountMean_tail S N a f hf C hfirstS).trans htail
  have h₂ : |B'-B|≤δ/6 := by
    rw [abs_sub_comm]
    exact (giantCandidateCountMean_tail T M a f hf C hfirstT).trans htail
  have h₃ : |A'-B'|≤δ/3+δ/3 :=
    (giantCandidateCountTruncatedMean_compare S T N M hC a b hR η hS hT h f hf).trans
      (add_le_add hpoint hpoly)
  change |A-B|≤δ
  have ht₁ := abs_sub_le A A' B
  have ht₂ := abs_sub_le A' B' B
  linarith only [ht₁,ht₂,h₁,h₂,h₃]

end
end ArtinMatthews
