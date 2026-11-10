module

public import ArtinMatthews.CubicSieveCorrectionModel
public import ArtinMatthews.GiantPrimeNormalization
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

/-! Uniform reciprocal mass of the actual top-down prime intervals. -/

noncomputable section
namespace ArtinMatthews

open Finset Filter
open scoped BigOperators Topology

theorem cubicSieve_block_eq_openBand {z : ℝ} (hz : 1 < z) (j : ℕ) :
    cubicSieveBlock z j =
      (Nat.primesLE ⌊z ^ ((1 / 2 : ℝ) ^ j)⌋₊).filter
        (fun p : ℕ => z ^ ((1 / 2 : ℝ) ^ (j + 1)) < (p : ℝ)) := by
  ext p
  have hn := Real.rpow_nonneg (zero_le_one.trans hz.le) ((1 / 2 : ℝ) ^ j)
  simp only [mem_cubicSieveBlock hz, mem_filter, Nat.mem_primesLE, Nat.le_floor_iff hn]
  tauto

theorem cubicSieve_block_prime_log_le {z : ℝ} (hz : 1 < z) {j p : ℕ}
    (hp : p ∈ cubicSieveBlock z j) :
    Real.log (p : ℝ) ≤ Real.log z * (1 / 2 : ℝ) ^ j := by
  obtain ⟨hprime, _, hhi⟩ := mem_cubicSieveBlock hz |>.mp hp
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have h := Real.log_le_log hp₀ hhi
  simpa only [Real.log_rpow (zero_lt_one.trans hz), mul_comm] using h

theorem cubicSieve_block_reciprocal_mass_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℝ, 1 < z → ∀ j : ℕ,
      (∑ p ∈ cubicSieveBlock z j, (1 : ℝ) / p) ≤ A := by
  have h := prime_reciprocal_power_interval_tendsto (a := (1 / 2 : ℝ)) (b := 1)
    (by norm_num) (by norm_num)
  have hC : ∀ᶠ u : ℝ in atTop,
      markedOpenBandMass (u ^ (1 / 2 : ℝ)) u ≤ Real.log 2 + 1 := by
    have hh := h.eventually (gt_mem_nhds (lt_add_of_pos_right (Real.log (1 / (1 / 2 : ℝ))) zero_lt_one))
    filter_upwards [hh] with u hu
    have hu' : markedOpenBandMass (u ^ (1 / 2 : ℝ)) (u ^ (1 : ℝ)) <
        Real.log (1 / (1 / 2 : ℝ)) + 1 := hu
    rw [Real.rpow_one, show (1 : ℝ) / (1 / 2) = 2 by norm_num] at hu'
    exact hu'.le
  obtain ⟨U, hU⟩ := eventually_atTop.mp hC
  let A := max (Real.log 2 + 1) (max U 1)
  refine ⟨A, zero_le_one.trans ((le_max_right U 1).trans (le_max_right _ _)), ?_⟩
  intro z hz j
  let u := z ^ ((1 / 2 : ℝ) ^ j)
  have hu : 0 ≤ u := Real.rpow_nonneg (zero_le_one.trans hz.le) _
  have he : z ^ ((1 / 2 : ℝ) ^ (j + 1)) = u ^ (1 / 2 : ℝ) := by
    unfold u
    rw [← Real.rpow_mul (zero_le_one.trans hz.le), pow_succ]
  by_cases hlarge : U ≤ u
  · rw [cubicSieve_block_eq_openBand hz, he]
    change markedOpenBandMass (u ^ (1 / 2 : ℝ)) u ≤ A
    exact (hU u hlarge).trans (le_max_left _ _)
  · have hsub : cubicSieveBlock z j ⊆ Icc 1 ⌊u⌋₊ := by
      intro p hp
      rw [cubicSieve_block_eq_openBand hz] at hp
      have hh := Nat.mem_primesLE.mp (mem_filter.mp hp).1
      exact mem_Icc.mpr ⟨hh.2.pos, hh.1⟩
    calc
      _ ≤ ∑ _p ∈ cubicSieveBlock z j, (1 : ℝ) := by
        apply sum_le_sum
        intro p hp
        have hprime := (mem_cubicSieveBlock hz |>.mp hp).1
        exact (div_le_one (by exact_mod_cast hprime.pos : (0 : ℝ) < p)).mpr
          (by exact_mod_cast hprime.one_lt.le)
      _ = ((cubicSieveBlock z j).card : ℝ) := by simp
      _ ≤ (⌊u⌋₊ : ℝ) := by
        have hcard := card_le_card hsub
        rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
        exact Nat.cast_le.mpr hcard
      _ ≤ u := Nat.floor_le hu
      _ ≤ A := (le_of_not_ge hlarge).trans ((le_max_left U 1).trans (le_max_right _ _))

theorem cubicSieve_block_divisorDensity_mass_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℝ, 1 < z → ∀ j : ℕ,
      (∑ p ∈ cubicSieveBlock z j, cubicSievePrimeDivisorDensity p) ≤ A := by
  obtain ⟨A, hA, hsum⟩ := cubicSieve_block_reciprocal_mass_bound
  refine ⟨2 * A, by positivity, ?_⟩
  intro z hz j
  calc
    _ ≤ ∑ p ∈ cubicSieveBlock z j, 2 * ((1 : ℝ) / p) := by
      apply sum_le_sum
      intro p hp
      simpa only [one_div] using
        (cubicSieve_primeDivisorDensity_bounds (mem_cubicSieveBlock hz |>.mp hp).1).2.2
    _ = 2 * (∑ p ∈ cubicSieveBlock z j, (1 : ℝ) / p) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hsum z hz j) (by norm_num)

end ArtinMatthews
