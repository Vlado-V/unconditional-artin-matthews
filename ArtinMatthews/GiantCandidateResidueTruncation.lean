module

public import ArtinMatthews.GiantCandidateResidueCRT
public import ArtinMatthews.RoughCharacterDensity
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The next Bonferroni layer is counted in the same prescribed residue
class, so its reciprocal mass carries the factor 1/Q. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateRoughResidueTruncation (P : Finset ℕ) (r M N Q a : ℕ) : ℂ :=
  ∑ n ∈ (Ioc M N).filter (fun n => Nat.ModEq Q n a),roughDivisorPolynomial P r n

theorem giantCandidateRoughResidueIoc_card_cast (P : Finset ℕ) (M N Q a : ℕ) :
    ((giantCandidateRoughResidueIoc P M N Q a).card:ℂ) =
      ∑ n ∈ (Ioc M N).filter (fun n => Nat.ModEq Q n a),
        if ∀ p ∈ P, ¬p ∣ n then (1:ℂ) else 0 := by
  unfold giantCandidateRoughResidueIoc
  rw [← sum_filter,sum_const,nsmul_eq_mul,mul_one]

theorem giantCandidateRoughResidueTruncation_error_le (P : Finset ℕ) (r M N Q a : ℕ)
    (hMN : M ≤ N) (hQ : 0 < Q) (hP : ∀ p∈P,p.Prime) (hcop : ∀ p∈P,p.Coprime Q) :
    ‖((giantCandidateRoughResidueIoc P M N Q a).card:ℂ) -
      giantCandidateRoughResidueTruncation P r M N Q a‖ ≤
      (((N-M:ℕ):ℝ)/(Q:ℝ))*(∑ S ∈ P.powersetCard (r+1),1/(roughSubsetDivisor S:ℝ)) +
        ((P.powersetCard (r+1)).card:ℝ) := by
  let A := (Ioc M N).filter (fun n => Nat.ModEq Q n a)
  let B := P.powersetCard (r+1)
  let H := ((N-M:ℕ):ℝ)/(Q:ℝ)
  rw [giantCandidateRoughResidueIoc_card_cast,giantCandidateRoughResidueTruncation,← sum_sub_distrib]
  change ‖∑ n ∈ A,((if ∀ p∈P,¬p∣n then (1:ℂ) else 0)-roughDivisorPolynomial P r n)‖ ≤
    H*(∑ S ∈ B,1/(roughSubsetDivisor S:ℝ))+(B.card:ℝ)
  calc
    _ ≤ ∑ n ∈ A, ∑ S ∈ B,if roughSubsetDivisor S ∣ n then (1:ℝ) else 0 :=
      (norm_sum_le _ _).trans (sum_le_sum (fun n _ => roughDivisorPolynomial_error_le P r n hP))
    _ = ∑ S ∈ B, ∑ n ∈ A,if roughSubsetDivisor S ∣ n then (1:ℝ) else 0 := sum_comm
    _ ≤ ∑ S ∈ B,(H/(roughSubsetDivisor S:ℝ)+1) := by
      apply sum_le_sum
      intro S hS
      have hsub := (mem_powersetCard.mp hS).1
      exact giantCandidate_divisor_residue_interval_le M N (roughSubsetDivisor S) Q a hMN
        (roughSubsetDivisor_pos S (fun p hp => hP p (hsub hp))) hQ
        (giantCandidateSubsetDivisor_coprime hsub hcop)
    _ = _ := by
      simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,mul_sum]
      congr 1
      apply sum_congr rfl
      intro S _
      ring

theorem giantCandidateRoughResidueTruncation_reindex (P : Finset ℕ) (r M N Q a : ℕ) :
    giantCandidateRoughResidueTruncation P r M N Q a =
      ∑ S ∈ roughTruncationSubsets P r,(-1:ℂ)^S.card *
        (((∑ n ∈ (Ioc M N).filter (fun n => Nat.ModEq Q n a),
          if roughSubsetDivisor S ∣ n then (1:ℝ) else 0):ℝ):ℂ) := by
  unfold giantCandidateRoughResidueTruncation roughDivisorPolynomial
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  rw [Complex.ofReal_sum,mul_sum]
  apply sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem giantCandidateRoughResidueDensityTruncation_eq (P : Finset ℕ) (r M N Q : ℕ) :
    (((((N-M:ℕ):ℝ)/(Q:ℝ))*roughCharacterDensityTruncation P r:ℝ):ℂ) =
      ∑ S ∈ roughTruncationSubsets P r,(-1:ℂ)^S.card *
        (((((N-M:ℕ):ℝ)/(Q:ℝ))/(roughSubsetDivisor S:ℝ):ℝ):ℂ) := by
  simp only [roughCharacterDensityTruncation,Complex.ofReal_mul,Complex.ofReal_sum,mul_sum,
    Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]
  apply sum_congr rfl
  intro S _
  ring

theorem giantCandidateRoughResidueTruncation_main_error_le (P : Finset ℕ) (r M N Q a : ℕ)
    (hMN : M ≤ N) (hQ : 0 < Q) (hP : ∀ p∈P,p.Prime) (hcop : ∀ p∈P,p.Coprime Q) :
    ‖giantCandidateRoughResidueTruncation P r M N Q a -
      (((((N-M:ℕ):ℝ)/(Q:ℝ))*roughCharacterDensityTruncation P r:ℝ):ℂ)‖ ≤
        ((roughTruncationSubsets P r).card:ℝ) := by
  rw [giantCandidateRoughResidueTruncation_reindex,giantCandidateRoughResidueDensityTruncation_eq,
    ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _S ∈ roughTruncationSubsets P r,(1:ℝ) := by
      apply sum_le_sum
      intro S hS
      rw [← mul_sub,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,← Complex.ofReal_sub,
        Complex.norm_real,Real.norm_eq_abs]
      have hsub := mem_powerset.mp (mem_filter.mp hS).1
      exact giantCandidate_divisor_residue_interval_error M N (roughSubsetDivisor S) Q a hMN
        (roughSubsetDivisor_pos S (fun p hp => hP p (hsub hp))) hQ
        (giantCandidateSubsetDivisor_coprime hsub hcop)
    _ = _ := by simp

end
end ArtinMatthews
