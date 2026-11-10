module

public import ArtinMatthews.RoughBonferroniDivisors
public import ArtinMatthews.MarkedProgressionCounting
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

/-! Each small-prime divisor condition meets an arbitrary candidate
residue class in a single CRT class, with a unit endpoint error. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateRoughResidueIoc (P : Finset ℕ) (M N Q a : ℕ) : Finset ℕ :=
  ((Ioc M N).filter (fun n => Nat.ModEq Q n a)).filter (fun n => ∀ p ∈ P, ¬p ∣ n)

theorem giantCandidateSubsetDivisor_coprime {P S : Finset ℕ} {Q : ℕ}
    (hS : S ⊆ P) (hcop : ∀ p ∈ P,p.Coprime Q) :
    (roughSubsetDivisor S).Coprime Q :=
  Nat.Coprime.prod_left (fun p hp => hcop p (hS hp))

theorem giantCandidate_divisor_residue_interval_error (M N d Q a : ℕ) (hMN : M ≤ N)
    (hd : 0 < d) (hQ : 0 < Q) (hcop : d.Coprime Q) :
    |(∑ n ∈ (Ioc M N).filter (fun n => Nat.ModEq Q n a),if d ∣ n then (1:ℝ) else 0) -
      ((N-M:ℕ):ℝ)/(Q:ℝ)/(d:ℝ)| ≤ 1 := by
  classical
  let b := Nat.chineseRemainder hcop 0 a
  have he (n : ℕ) : (Nat.ModEq Q n a ∧ d ∣ n) ↔ Nat.ModEq (d*Q) n b := by
    constructor
    · rintro ⟨hn,hdn⟩
      exact Nat.chineseRemainder_modEq_unique hcop (Nat.modEq_zero_iff_dvd.mpr hdn) hn
    · intro hn
      obtain ⟨hn₁,hn₂⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mpr hn
      exact ⟨hn₂.trans b.property.2,Nat.modEq_zero_iff_dvd.mp (hn₁.trans b.property.1)⟩
  have hset : (((Ioc M N).filter (fun n => Nat.ModEq Q n a)).filter (fun n => d ∣ n)) =
      (Ioc M N).filter (fun n => Nat.ModEq (d*Q) n b) := by
    ext n
    simp only [mem_filter, and_assoc, he]
  rw [← sum_filter,hset,sum_const,nsmul_eq_mul,mul_one,Nat.cast_sub hMN]
  have hden : ((N:ℝ)-(M:ℝ))/(Q:ℝ)/(d:ℝ) = ((N:ℝ)-(M:ℝ))/((d*Q:ℕ):ℝ) := by
    push_cast
    ring
  rw [hden]
  exact marked_interval_residue_error M N (d*Q) b hMN (Nat.mul_pos hd hQ)

theorem giantCandidate_divisor_residue_interval_le (M N d Q a : ℕ) (hMN : M ≤ N)
    (hd : 0 < d) (hQ : 0 < Q) (hcop : d.Coprime Q) :
    (∑ n ∈ (Ioc M N).filter (fun n => Nat.ModEq Q n a),if d ∣ n then (1:ℝ) else 0) ≤
      ((N-M:ℕ):ℝ)/(Q:ℝ)/(d:ℝ)+1 := by
  have h := (abs_le.mp (giantCandidate_divisor_residue_interval_error M N d Q a hMN hd hQ hcop)).2
  linarith only [h]

end
end ArtinMatthews
