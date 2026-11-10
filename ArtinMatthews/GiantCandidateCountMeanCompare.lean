module

public import ArtinMatthews.GiantCandidateCountMeanRemainder
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

/-! Comparison of one exact-count probability using only a fixed
finite collection of mixed binomial moments. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giantCandidateCountPolyMean_compare {ι Ω Ξ : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset Ω) (T : Finset Ξ) (N : Ω → ι → ℕ) (M : Ξ → ι → ℕ)
    (k : ι → ℕ) (b : ℕ) (η : ℝ)
    (h : ∀ l∈giantCandidateCountVectors ι (2*b),
      |giantCandidateCountMoment S N (fun i => k i+l i)-
        giantCandidateCountMoment T M (fun i => k i+l i)|≤η) :
    |(𝔼 t∈S,giantCandidateCountVectorPoly k b (N t))-
      (𝔼 t∈T,giantCandidateCountVectorPoly k b (M t))| ≤
        (∑ l∈giantCandidateCountVectors ι (2*b),|giantCandidateCountPolyCoeff k l|)*η := by
  rw [giantCandidateCountVectorPoly_mean_eq S N k b,
    giantCandidateCountVectorPoly_mean_eq T M k b,← sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ l∈giantCandidateCountVectors ι (2*b),|giantCandidateCountPolyCoeff k l| * 
        |giantCandidateCountMoment S N (fun i => k i+l i)-
          giantCandidateCountMoment T M (fun i => k i+l i)| := by
      simp only [← abs_mul]
      exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ l∈giantCandidateCountVectors ι (2*b),|giantCandidateCountPolyCoeff k l| * η :=
      sum_le_sum (fun l hl => mul_le_mul_of_nonneg_left (h l hl) (abs_nonneg _))
    _ = _ := by rw [sum_mul]

theorem giantCandidateCountDeltaMean_compare {ι Ω Ξ : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset Ω) (T : Finset Ξ) (N : Ω → ι → ℕ) (M : Ξ → ι → ℕ)
    {C : ℝ} (hC : 0≤C) {a : ℕ} (k : ι → ℕ) (hk : ∀ i,k i≤a)
    (b : ℕ) (hR : giantCandidateCountRemainderScale C a (2*b+1)≤1)
    (η : ℝ)
    (hS : ∀ l∈giantCandidateCountVectors ι (a+2*b+1),
      giantCandidateCountMoment S N l≤2*giantCandidateMomentEnvelope C l)
    (hT : ∀ l∈giantCandidateCountVectors ι (a+2*b+1),
      giantCandidateCountMoment T M l≤2*giantCandidateMomentEnvelope C l)
    (h : ∀ l∈giantCandidateCountVectors ι (a+2*b+1),
      |giantCandidateCountMoment S N l-giantCandidateCountMoment T M l|≤η) :
    |(𝔼 t∈S,giantCandidateCountVectorDelta k (N t))-
      (𝔼 t∈T,giantCandidateCountVectorDelta k (M t))| ≤
      2*(2*(2:ℝ)^Fintype.card ι*giantCandidateCountRemainderScale C a (2*b+1))+
        (∑ l∈giantCandidateCountVectors ι (2*b),|giantCandidateCountPolyCoeff k l|)*η := by
  let δS := 𝔼 t∈S,giantCandidateCountVectorDelta k (N t)
  let δT := 𝔼 t∈T,giantCandidateCountVectorDelta k (M t)
  let PS := 𝔼 t∈S,giantCandidateCountVectorPoly k b (N t)
  let PT := 𝔼 t∈T,giantCandidateCountVectorPoly k b (M t)
  let R := 2*(2:ℝ)^Fintype.card ι*giantCandidateCountRemainderScale C a (2*b+1)
  have horders (A : Finset ι) : giantCandidateCountErrorOrders k (2*b+1) A ∈
      giantCandidateCountVectors ι (a+2*b+1) := by
    apply mem_giantCandidateCountVectors.mpr
    intro i
    unfold giantCandidateCountErrorOrders
    have hi := hk i
    split_ifs <;> omega
  have h₁ : |δS-PS|≤R := giantCandidateCountVectorMeanPoly_error S N hC k hk b hR
    (fun A _ => hS _ (horders A))
  have h₂ : |PT-δT|≤R := by
    rw [abs_sub_comm]
    exact giantCandidateCountVectorMeanPoly_error T M hC k hk b hR (fun A _ => hT _ (horders A))
  have h₃ : |PS-PT| ≤
      (∑ l∈giantCandidateCountVectors ι (2*b),|giantCandidateCountPolyCoeff k l|)*η :=
    giantCandidateCountPolyMean_compare S T N M k b η (fun l hl => h _ (by
      apply mem_giantCandidateCountVectors.mpr
      intro i
      have hi := hk i
      have hj := mem_giantCandidateCountVectors.mp hl i
      omega))
  change |δS-δT| ≤ 2*R+(∑ l∈giantCandidateCountVectors ι (2*b),|giantCandidateCountPolyCoeff k l|)*η
  have htriangle₁ := abs_sub_le δS PS δT
  have htriangle₂ := abs_sub_le PS PT δT
  linarith only [htriangle₁,htriangle₂,h₁,h₂,h₃]

end
end ArtinMatthews
