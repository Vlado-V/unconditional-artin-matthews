module

public import ArtinMatthews.CubicSieveEulerPower
public import ArtinMatthews.CubicSieveDivisorCoprimeMain
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual principal marking factor and its first derivative. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveCoprimeEulerFactor (d : ℕ) (s : ℝ) : ℝ :=
  ∑ T ∈ d.primeFactors.powerset, (-1 : ℝ) ^ T.card *
    cubicSieveEulerPower (roughSubsetDivisor T) s

theorem cubicSieve_coprimeEulerFactor_eq_prod (d : ℕ) (s : ℝ) :
    cubicSieveCoprimeEulerFactor d s = ∏ p ∈ d.primeFactors, (1 - cubicSieveEulerPower p s) := by
  rw [show (∏ p ∈ d.primeFactors, (1 - cubicSieveEulerPower p s)) =
    ∏ p ∈ d.primeFactors, (1 + -cubicSieveEulerPower p s) by simp only [sub_eq_add_neg], prod_one_add]
  unfold cubicSieveCoprimeEulerFactor
  apply sum_congr rfl
  intro T hT
  rw [cubicSieve_eulerPower_prod T
    (fun p hp => (Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp)).pos),
    prod_neg]

theorem cubicSieve_coprimeEulerFactor_one (d : ℕ) :
    cubicSieveCoprimeEulerFactor d 1 = cubicSieveCoprimeDensity d := by
  rw [cubicSieve_coprimeEulerFactor_eq_prod]
  apply prod_congr rfl
  intro p hp
  rw [cubicSieve_eulerPower_one (Nat.prime_of_mem_primeFactors hp).pos]

theorem cubicSieve_coprimeEulerFactor_hasDerivAt_one (d : ℕ) :
    HasDerivAt (cubicSieveCoprimeEulerFactor d) (-cubicSieveCoprimeLogMoment d) 1 := by
  have h := HasDerivAt.fun_sum (u := d.primeFactors.powerset) (fun T _ =>
    (cubicSieve_eulerPower_hasDerivAt (roughSubsetDivisor T) 1).const_mul ((-1 : ℝ) ^ T.card))
  convert h using 1
  · rfl
  · rw [cubicSieveCoprimeLogMoment, ← sum_neg_distrib]
    apply sum_congr rfl
    intro T hT
    rw [cubicSieve_eulerPower_one
      (roughSubsetDivisor_pos T (fun p hp => Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp)))]
    ring

def cubicSieveMarkingFactor (d : ℕ) (s : ℝ) : ℝ :=
  cubicSieveCoprimeEulerFactor d s ^ 2 / (d.totient : ℝ)

theorem cubicSieve_markingFactor_one {d : ℕ} (hd : 0 < d) :
    cubicSieveMarkingFactor d 1 = cubicSieveCoprimeDensity d / (d : ℝ) := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hφ : (d.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hd).ne'
  rw [cubicSieveMarkingFactor, cubicSieve_coprimeEulerFactor_one, cubicSieve_coprimeDensity_eq_totient hd.ne']
  field_simp

theorem cubicSieve_markingFactor_hasDerivAt_one {d : ℕ} (hd : 0 < d) :
    HasDerivAt (cubicSieveMarkingFactor d) (-2 * cubicSieveCoprimeLogMoment d / (d : ℝ)) 1 := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hφ : (d.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hd).ne'
  have h := ((cubicSieve_coprimeEulerFactor_hasDerivAt_one d).pow 2).div_const (d.totient : ℝ)
  convert h using 1
  · rfl
  · rw [cubicSieve_coprimeEulerFactor_one, cubicSieve_coprimeDensity_eq_totient hd.ne']
    norm_num
    field_simp

end ArtinMatthews
