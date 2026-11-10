module

public import ArtinMatthews.CubicSieveDivisorConvolution
public import Mathlib.Data.ZMod.Basic
public import ArtinMatthews.MarkedMajorArcDivisorReindex
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The exact weighted progression after removing the squarefree divisor.
The test is evaluated at the original integer, including its shift by one. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveShiftedDivisorProgression (d r X : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 X, if r ∣ n ∧ d ∣ n - 1 then (n.divisors.card : ℝ) * w n else 0

theorem cubicSieve_shifted_residue_iff {d n : ℕ} (hn : 1 ≤ n) :
    d ∣ n - 1 ↔ Nat.ModEq d n 1 := by
  have h : n - 1 + 1 = n := Nat.sub_add_cancel hn
  constructor
  · intro hd
    simpa only [h, zero_add] using (Nat.modEq_zero_iff_dvd.mpr hd).add_right 1
  · intro hm
    apply Nat.modEq_zero_iff_dvd.mp
    apply Nat.ModEq.add_right_cancel' 1
    simpa only [h, zero_add] using hm

theorem cubicSieve_shiftedDivisorProgression_of_not_coprime {d r X : ℕ}
    (hc : ¬ d.Coprime r) (w : ℕ → ℝ) :
    cubicSieveShiftedDivisorProgression d r X w = 0 := by
  unfold cubicSieveShiftedDivisorProgression
  apply sum_eq_zero
  intro n hn
  have hpos : 1 ≤ n := (mem_Ioc.mp hn).1
  apply ite_eq_right
  rintro ⟨hr, hd⟩
  exact hc (marked_divisor_coprime hd (by simpa only [Nat.sub_add_cancel hpos] using hr))

theorem cubicSieve_shiftedDivisorProgression_expand {r : ℕ} (hr : Squarefree r)
    (d X : ℕ) (w : ℕ → ℝ) :
    cubicSieveShiftedDivisorProgression d r X w =
      ∑ T ∈ r.primeFactors.powerset, cubicSieveDivisorEulerCoeff r.primeFactors T *
        ∑ k ∈ Ioc 0 (X / (r * roughSubsetDivisor T)),
          if d ∣ (r * roughSubsetDivisor T) * k - 1 then
            (k.divisors.card : ℝ) * w ((r * roughSubsetDivisor T) * k) else 0 := by
  let w' (n : ℕ) := if d ∣ n - 1 then w n else 0
  have hsplit (n : ℕ) :
      (if r ∣ n ∧ d ∣ n - 1 then (n.divisors.card : ℝ) * w n else 0) =
        (if r ∣ n then (n.divisors.card : ℝ) else 0) * w' n := by
    by_cases hrn : r ∣ n <;> by_cases hdn : d ∣ n - 1 <;> simp [w', hrn, hdn]
  unfold cubicSieveShiftedDivisorProgression
  simp_rw [hsplit, cubicSieve_divisorCount_squarefree_shift hr, sum_mul, mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  let a := r * roughSubsetDivisor T
  have ha : 0 < a := Nat.mul_pos (Nat.pos_of_ne_zero hr.ne_zero)
    (roughSubsetDivisor_pos T
      (fun _ hp => Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp)))
  rw [← mul_sum]
  congr 1
  simp_rw [← Nat.mul_assoc r (roughSubsetDivisor T)]
  change (∑ n ∈ Ioc 0 X, cubicSieveDivisorShift a (fun k => (k.divisors.card : ℝ)) n * w' n) =
    ∑ k ∈ Ioc 0 (X / a), if d ∣ a * k - 1 then (k.divisors.card : ℝ) * w (a * k) else 0
  rw [show (∑ n ∈ Ioc 0 X,
      cubicSieveDivisorShift a (fun k => (k.divisors.card : ℝ)) n * w' n) =
        ∑ n ∈ Ioc 0 X, if a ∣ n then ((n / a).divisors.card : ℝ) * w' n else 0 by
    simp only [cubicSieveDivisorShift, ite_mul, zero_mul]]
  rw [marked_sum_Ioc_dvd_reindex ha]
  simp only [Nat.zero_div, Nat.mul_div_cancel_left _ ha, w', mul_ite, mul_zero]

theorem cubicSieve_unit_progression_quotient {d a : ℕ} (ha : a.Coprime d)
    (u : (ZMod d)ˣ) (k : ℕ) :
    ((a * k : ℕ) : ZMod d) = (u : ZMod d) ↔
      (k : ZMod d) = (((ZMod.unitOfCoprime a ha)⁻¹ * u : (ZMod d)ˣ) : ZMod d) := by
  rw [Nat.cast_mul, ← ZMod.coe_unitOfCoprime a ha, Units.val_mul]
  exact (Units.eq_inv_mul_iff_mul_eq _).symm

theorem cubicSieve_divisorShift_coprime_modulus {d r : ℕ}
    (hc : d.Coprime r) {T : Finset ℕ} (hT : T ⊆ r.primeFactors) :
    (r * roughSubsetDivisor T).Coprime d := by
  have hdiv : roughSubsetDivisor T ∣ r :=
    (roughSubsetDivisor_dvd_iff T r (fun _ hp => Nat.prime_of_mem_primeFactors (hT hp))).mpr
      (fun _ hp => Nat.dvd_of_mem_primeFactors (hT hp))
  exact hc.symm.mul_left (hc.symm.of_dvd_left hdiv)

end ArtinMatthews
