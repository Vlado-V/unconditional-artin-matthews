module

public import ArtinMatthews.GiantCandidateCountVectorPoly
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
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

/-! Real expectations of the finite binomial tests and their
factorial moment envelope. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateCountMoment {ι Ω : Type*} [Fintype ι] (S : Finset Ω)
    (N : Ω → ι → ℕ) (k : ι → ℕ) : ℝ :=
  𝔼 t∈S,giantCandidateCountBinomialTest k (N t)

def giantCandidateMomentEnvelope {ι : Type*} [Fintype ι] (C : ℝ) (k : ι → ℕ) : ℝ :=
  ∏ i,C^(k i)/((k i).factorial:ℝ)

theorem giantCandidateCountMoment_one_coordinate {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset Ω) (N : Ω → ι → ℕ) (i : ι) :
    giantCandidateCountMoment S N (fun l => if l=i then 1 else 0) =
      𝔼 t∈S,(N t i:ℝ) := by
  unfold giantCandidateCountMoment giantCandidateCountBinomialTest
  apply expect_congr rfl
  intro t _
  rw [← mul_prod_erase univ (fun l => ((N t l).choose (if l=i then 1 else 0):ℝ)) (mem_univ i)]
  have hprod : (∏ l∈univ.erase i,((N t l).choose (if l=i then 1 else 0):ℝ)) = 1 := by
    calc
      _ = ∏ _l∈univ.erase i,(1:ℝ) := by
        apply prod_congr rfl
        intro l hl
        simp only [ite_eq_right (mem_erase.mp hl).1,Nat.choose_zero_right,Nat.cast_one]
      _ = _ := prod_const_one
  rw [ite_eq_left rfl,Nat.choose_one_right,hprod,mul_one]

theorem giantCandidateMomentEnvelope_one_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ℝ) (i : ι) :
    giantCandidateMomentEnvelope C (fun l => if l=i then 1 else 0) = C := by
  unfold giantCandidateMomentEnvelope
  rw [← mul_prod_erase univ
    (fun l => C^(if l=i then 1 else 0:ℕ)/((if l=i then 1 else 0:ℕ).factorial:ℝ)) (mem_univ i)]
  have hprod : (∏ l∈univ.erase i,C^(if l=i then 1 else 0:ℕ)/((if l=i then 1 else 0:ℕ).factorial:ℝ)) = 1 := by
    calc
      _ = ∏ _l∈univ.erase i,(1:ℝ) := by
        apply prod_congr rfl
        intro l hl
        simp only [ite_eq_right (mem_erase.mp hl).1,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one]
      _ = _ := prod_const_one
  rw [ite_eq_left rfl,pow_one,Nat.factorial_one,Nat.cast_one,div_one,hprod,mul_one]

theorem giantCandidateCountVectorPoly_mean_eq {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset Ω) (N : Ω → ι → ℕ) (k : ι → ℕ) (b : ℕ) :
    (𝔼 t∈S,giantCandidateCountVectorPoly k b (N t)) =
      ∑ l∈giantCandidateCountVectors ι (2*b),giantCandidateCountPolyCoeff k l*
        giantCandidateCountMoment S N (fun i => k i+l i) := by
  simp_rw [giantCandidateCountVectorPoly_eq_sum,expect_sum_comm,← mul_expect,giantCandidateCountMoment]

end
end ArtinMatthews
