module

public import ArtinMatthews.RoughBonferroniDivisors
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.NumberTheory.Harmonic.Defs
public import ArtinMatthews.MarkedMajorArcDivisorReindex
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
public import Mathlib.NumberTheory.Harmonic.Bounds
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

/-! Inclusion-exclusion for the two finite coprime terms of the hyperbola. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

theorem cubicSieve_coprime_indicator {d : ℕ} (hd : d ≠ 0) (n : ℕ) :
    (if n.Coprime d then (1 : ℝ) else 0) =
      ∑ T ∈ d.primeFactors.powerset,
        if roughSubsetDivisor T ∣ n then (-1 : ℝ) ^ T.card else 0 := by
  let P := d.primeFactors
  let g (p : ℕ) : ℝ := if p ∣ n then -1 else 0
  calc
    _ = ∏ p ∈ P, (1 + g p) := by
      by_cases hc : n.Coprime d
      · rw [ite_eq_left hc]
        apply (prod_eq_one ?_).symm
        intro p hp
        have h : ¬p ∣ n := fun h =>
          (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, Nat.prime_of_mem_primeFactors hp,
            h, Nat.dvd_of_mem_primeFactors hp⟩) hc
        simp only [g, ite_eq_right h, add_zero]
      · rw [ite_eq_right hc]
        obtain ⟨p, hp, hpn, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
        exact (prod_eq_zero (Nat.mem_primeFactors.mpr ⟨hp, hpd, hd⟩) (by
          simp only [g, ite_eq_left hpn, add_neg_cancel])).symm
    _ = ∑ T ∈ P.powerset, ∏ p ∈ T, g p := prod_one_add P
    _ = _ := by
      apply sum_congr rfl
      intro T hT
      have hprime (p : ℕ) (hp : p ∈ T) : p.Prime :=
        Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp)
      simp only [g, prod_ite_zero, prod_const, roughSubsetDivisor_dvd_iff T n hprime]

private theorem cubicSieve_Ioc_eq_Icc (X : ℕ) : Ioc 0 X = Icc 1 X := by
  ext n
  simp only [mem_Ioc, mem_Icc]
  omega

theorem cubicSieve_sum_coprime {d : ℕ} (hd : d ≠ 0) (X : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ (Icc 1 X).filter (fun n => n.Coprime d), w n) =
      ∑ T ∈ d.primeFactors.powerset, (-1 : ℝ) ^ T.card *
        ∑ k ∈ Icc 1 (X / roughSubsetDivisor T), w (roughSubsetDivisor T * k) := by
  rw [sum_filter]
  simp_rw [← cubicSieve_Ioc_eq_Icc]
  calc
    _ = ∑ n ∈ Ioc 0 X, (if n.Coprime d then (1 : ℝ) else 0) * w n := by
      simp only [ite_mul, one_mul, zero_mul]
    _ = _ := by
      simp_rw [cubicSieve_coprime_indicator hd, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro T hT
      have hpos := roughSubsetDivisor_pos T
        (fun _ hp => Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp))
      simp only [ite_mul, zero_mul]
      rw [marked_sum_Ioc_dvd_reindex hpos, Nat.zero_div, mul_sum]

theorem cubicSieve_coprime_harmonic_eq {d : ℕ} (hd : d ≠ 0) (X : ℕ) :
    (∑ n ∈ (Icc 1 X).filter (fun n => n.Coprime d), (n : ℝ)⁻¹) =
      ∑ T ∈ d.primeFactors.powerset, ((-1 : ℝ) ^ T.card / roughSubsetDivisor T) *
        (harmonic (X / roughSubsetDivisor T) : ℝ) := by
  rw [cubicSieve_sum_coprime hd]
  apply sum_congr rfl
  intro T _
  simp only [Nat.cast_mul, mul_inv, ← mul_sum, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, div_eq_mul_inv, mul_assoc]

theorem cubicSieve_coprime_card_eq {d : ℕ} (hd : d ≠ 0) (X : ℕ) :
    (((Icc 1 X).filter (fun n => n.Coprime d)).card : ℝ) =
      ∑ T ∈ d.primeFactors.powerset, (-1 : ℝ) ^ T.card * ((X / roughSubsetDivisor T : ℕ) : ℝ) := by
  calc
    _ = ∑ _n ∈ (Icc 1 X).filter (fun n => n.Coprime d), (1 : ℝ) := by simp
    _ = _ := by
      rw [cubicSieve_sum_coprime hd]
      apply sum_congr rfl
      intro T _
      simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel]

theorem cubicSieve_coprime_density_eq (P : Finset ℕ) :
    (∑ T ∈ P.powerset, (-1 : ℝ) ^ T.card / roughSubsetDivisor T) =
      ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
  rw [show (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) = ∏ p ∈ P, (1 + (-(p : ℝ)⁻¹)) by
    simp only [sub_eq_add_neg], prod_one_add]
  apply sum_congr rfl
  intro T _
  simp only [roughSubsetDivisor, Nat.cast_prod, ← prod_const, div_eq_mul_inv, ← prod_inv_distrib,
    ← prod_mul_distrib, neg_one_mul]

end ArtinMatthews
