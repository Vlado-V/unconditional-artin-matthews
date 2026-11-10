module

public import ArtinMatthews.CubicSieveDivisorRealModel
public import ArtinMatthews.CubicSieveDivisorProgression
public import ArtinMatthews.CubicSieveDivisorShiftedEstimate
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Real-cutoff progression prefixes with the original squarefree divisor
and the exact logarithmic main terms of its signed shifts. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveShiftedDivisorCoefficient (d r n : ℕ) : ℝ :=
  if r ∣ n ∧ d ∣ n - 1 then (n.divisors.card : ℝ) else 0

def cubicSieveShiftedDivisorLogModel (d r : ℕ) (t : ℝ) : ℝ :=
  ∑ T ∈ r.primeFactors.powerset, cubicSieveDivisorEulerCoeff r.primeFactors T *
    cubicSieveDivisorUnitModel d (t / ((r * roughSubsetDivisor T : ℕ) : ℝ))

def cubicSieveShiftedDivisorLogDensity (d r : ℕ) (t : ℝ) : ℝ :=
  ∑ T ∈ r.primeFactors.powerset, cubicSieveDivisorEulerCoeff r.primeFactors T *
    (cubicSieveDivisorUnitDensity d (t / ((r * roughSubsetDivisor T : ℕ) : ℝ)) /
      ((r * roughSubsetDivisor T : ℕ) : ℝ))

private theorem cubicSieve_divisorShift_range {r : ℕ} (hr : r ≠ 0)
    {T : Finset ℕ} (hT : T ∈ r.primeFactors.powerset) :
    0 < r * roughSubsetDivisor T ∧ r ≤ r * roughSubsetDivisor T ∧
      r * roughSubsetDivisor T ≤ r ^ 2 := by
  have hP (p : ℕ) (hp : p ∈ T) : p.Prime :=
    Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp)
  have hpos := roughSubsetDivisor_pos T hP
  have hdiv := (roughSubsetDivisor_dvd_iff T r hP).mpr
    (fun _ hp => Nat.dvd_of_mem_primeFactors (mem_powerset.mp hT hp))
  have hr₀ := Nat.pos_of_ne_zero hr
  exact ⟨Nat.mul_pos hr₀ hpos, Nat.le_mul_of_pos_right r hpos, by
    rw [pow_two]
    exact Nat.mul_le_mul_left r (Nat.le_of_dvd hr₀ hdiv)⟩

theorem cubicSieve_shiftedDivisorCoefficient_prefix (d r X : ℕ) :
    (∑ n ∈ Icc 0 X, cubicSieveShiftedDivisorCoefficient d r n) =
      cubicSieveShiftedDivisorProgression d r X (fun _ => 1) := by
  rw [Icc_eq_cons_Ioc (Nat.zero_le X), sum_cons]
  simp only [cubicSieveShiftedDivisorCoefficient, cubicSieveShiftedDivisorProgression,
    Nat.divisors_zero, card_empty, Nat.cast_zero, ite_self, zero_add, mul_one]

theorem cubicSieve_shiftedDivisorRow_eq_unitCount {d a : ℕ} (ha : 0 < a)
    (hc : a.Coprime d) (N : ℕ) :
    (∑ k ∈ Ioc 0 N, if d ∣ a * k - 1 then (k.divisors.card : ℝ) else 0) =
      cubicSieveDivisorUnitCount d N ((ZMod.unitOfCoprime a hc)⁻¹ * 1) := by
  have hI : Ioc 0 N = Icc 1 N := by
    ext k
    simp only [mem_Ioc, mem_Icc]
    omega
  rw [cubicSieveDivisorUnitCount, hI]
  apply sum_congr rfl
  intro k hk
  have hclass : d ∣ a * k - 1 ↔
      (k : ZMod d) = ((((ZMod.unitOfCoprime a hc)⁻¹ * 1) : (ZMod d)ˣ) : ZMod d) := by
    rw [cubicSieve_shifted_residue_iff (Nat.mul_pos ha (mem_Icc.mp hk).1),
      ← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
    exact cubicSieve_unit_progression_quotient hc 1 k
  simp only [hclass, mul_ite, mul_one, mul_zero]

theorem cubicSieve_shiftedDivisorLogModel_hasDerivAt {d r : ℕ}
    (hd : 0 < d) (hr : r ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (cubicSieveShiftedDivisorLogModel d r) (cubicSieveShiftedDivisorLogDensity d r t) t := by
  unfold cubicSieveShiftedDivisorLogModel cubicSieveShiftedDivisorLogDensity
  apply HasDerivAt.fun_sum
  intro T hT
  let a := r * roughSubsetDivisor T
  have ha : (0 : ℝ) < a := by exact_mod_cast (cubicSieve_divisorShift_range hr hT).1
  have h := ((cubicSieve_divisorUnitModel_hasDerivAt d hd (div_pos ht ha)).comp t
    ((hasDerivAt_id t).div_const (a : ℝ))).const_mul
      (cubicSieveDivisorEulerCoeff r.primeFactors T)
  simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using h

theorem cubicSieve_shiftedDivisorLogDensity_continuousOn {d r : ℕ} (hr : r ≠ 0) :
    ContinuousOn (cubicSieveShiftedDivisorLogDensity d r) (Set.Ioi 0) := by
  unfold cubicSieveShiftedDivisorLogDensity
  apply continuousOn_finsetSum
  intro T hT
  let a := r * roughSubsetDivisor T
  have ha : (0 : ℝ) < a := by exact_mod_cast (cubicSieve_divisorShift_range hr hT).1
  have hlog : ContinuousOn (fun t : ℝ => Real.log (t / (a : ℝ))) (Set.Ioi 0) := by
    intro t ht
    have hdiv : ContinuousAt (fun t : ℝ => t / (a : ℝ)) t :=
      continuousAt_id.div_const (a : ℝ)
    exact (ContinuousAt.comp (f := fun v : ℝ => v / (a : ℝ))
      (Real.continuousAt_log (div_pos ht ha).ne') hdiv).continuousWithinAt
  exact (((((hlog.add continuousOn_const).mul continuousOn_const).sub
    continuousOn_const).div_const (d : ℝ)).div_const (a : ℝ)).const_mul _

theorem cubicSieve_shiftedDivisorProgression_real_model_error {d r : ℕ} (hd : 0 < d)
    (hr : Squarefree r) (hc : d.Coprime r) {t : ℝ}
    (ht : (d : ℝ) ^ 2 * (r : ℝ) ^ 2 ≤ t) :
    |cubicSieveShiftedDivisorProgression d r ⌊t⌋₊ (fun _ => 1) -
      cubicSieveShiftedDivisorLogModel d r t| ≤
      34 * (2 : ℝ) ^ d.primeFactors.card * (3 : ℝ) ^ r.primeFactors.card *
        Real.sqrt (t / (r : ℝ)) := by
  have ht₀ : 0 ≤ t := (by positivity : 0 ≤ (d : ℝ) ^ 2 * (r : ℝ) ^ 2).trans ht
  have hr₀ : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr.ne_zero
  rw [cubicSieve_shiftedDivisorProgression_expand hr, cubicSieveShiftedDivisorLogModel,
    ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ T ∈ r.primeFactors.powerset, |cubicSieveDivisorEulerCoeff r.primeFactors T| *
        (34 * (2 : ℝ) ^ d.primeFactors.card * Real.sqrt (t / (r : ℝ))) := by
      apply sum_le_sum
      intro T hT
      let a := r * roughSubsetDivisor T
      obtain ⟨hapos, hra, har⟩ := cubicSieve_divisorShift_range hr.ne_zero hT
      have ha : (0 : ℝ) < a := by exact_mod_cast hapos
      have hacop : a.Coprime d := cubicSieve_divisorShift_coprime_modulus hc (mem_powerset.mp hT)
      have hta : (d : ℝ) ^ 2 ≤ t / (a : ℝ) := (le_div_iff₀ ha).mpr
        ((mul_le_mul_of_nonneg_left (by exact_mod_cast har) (sq_nonneg (d : ℝ))).trans ht)
      have hmono : t / (a : ℝ) ≤ t / (r : ℝ) :=
        div_le_div_of_nonneg_left ht₀ hr₀ (Nat.cast_le.mpr hra)
      change |cubicSieveDivisorEulerCoeff r.primeFactors T *
        (∑ k ∈ Ioc 0 (⌊t⌋₊ / a), if d ∣ a * k - 1 then (k.divisors.card : ℝ) * 1 else 0) -
        cubicSieveDivisorEulerCoeff r.primeFactors T * cubicSieveDivisorUnitModel d (t / (a : ℝ))| ≤ _
      simp only [mul_one]
      rw [cubicSieve_shiftedDivisorRow_eq_unitCount hapos hacop, ← Nat.floor_div_natCast,
        ← mul_sub, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (cubicSieve_divisorUnitCount_real_model_error hd hta _).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) (by positivity))
    _ = _ := by rw [← sum_mul, cubicSieve_divisorEulerCoeff_abs_sum]; ring

end ArtinMatthews
