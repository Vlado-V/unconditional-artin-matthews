module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! The exact classical reciprocal-prime input and its sole required scale.

Published source: J. B. Rosser and L. Schoenfeld, *Approximate formulas for
some functions of prime numbers*, Illinois J. Math. 6 (1962), 64–94,
Theorem 5, (3.17)–(3.18), bounded-error consequence of Mertens' second
theorem. DOI: https://doi.org/10.1215/ijm/1255631807.
The formal proof uses the bounded-error statement
`RS_prime.mertens_second_theorem'`. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def sievePrimesUpTo (y : ℝ) : Finset ℕ := (Iic ⌊y⌋₊).filter Nat.Prime

/-- The bounded-error consequence of published Mertens' second theorem,
stated exactly as the existing library declaration except for this name. -/
def PrimeReciprocalInput : Prop :=
  ∃ C : ℝ, ∀ y : ℝ, 2 ≤ y →
    |(∑ p ∈ sievePrimesUpTo y, 1 / (p : ℝ)) - Real.log (Real.log y)| ≤ C

lemma sievePrimesUpTo_prime (y : ℝ) (p : ℕ) (hp : p ∈ sievePrimesUpTo y) :
    Nat.Prime p := (mem_filter.mp hp).2

lemma sievePrimesUpTo_le (y : ℝ) (hy : 0 ≤ y) (p : ℕ)
    (hp : p ∈ sievePrimesUpTo y) : (p : ℝ) ≤ y := by
  exact (Nat.le_floor_iff hy).mp (mem_Iic.mp (mem_filter.mp hp).1)

lemma sievePrimesUpTo_card_le (y : ℝ) (hy : 0 ≤ y) :
    ((sievePrimesUpTo y).card : ℝ) ≤ y := by
  have hs : sievePrimesUpTo y ⊆ Icc 1 ⌊y⌋₊ := by
    intro p hp
    exact mem_Icc.mpr ⟨(sievePrimesUpTo_prime y p hp).pos,
      mem_Iic.mp (mem_filter.mp hp).1⟩
  have hc : (sievePrimesUpTo y).card ≤ ⌊y⌋₊ := by
    simpa using card_le_card hs
  exact (show ((sievePrimesUpTo y).card : ℝ) ≤ (⌊y⌋₊ : ℝ) by exact_mod_cast hc).trans
    (Nat.floor_le hy)

/-- Precisely the prime reciprocal bounds used in the rough sieve, at
`y=exp(L^.99)`. The upper coefficient leaves room below `5/4`. -/
theorem PrimeReciprocalInput.rough_scale (hM : PrimeReciprocalInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ L : ℝ in atTop,
      (99 / 100 : ℝ) * Real.log L - C ≤
        ∑ p ∈ sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ))), 1 / (p : ℝ) ∧
      (∑ p ∈ sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ))), 1 / (p : ℝ)) ≤
        (5 / 4 : ℝ) * Real.log L := by
  obtain ⟨C, hC⟩ := hM
  have hC₀ : 0 ≤ C := (abs_nonneg _).trans (hC 2 (by norm_num))
  refine ⟨C, hC₀, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp (4 * C + 1))] with L hL
  have hL₁ : 1 ≤ L := (Real.one_le_exp (by linarith)).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL₁
  have hlog : 4 * C + 1 ≤ Real.log L := by
    rw [← Real.log_exp (4 * C + 1)]
    exact Real.log_le_log (Real.exp_pos _) hL
  have hX : 1 ≤ L ^ (99 / 100 : ℝ) := Real.one_le_rpow hL₁ (by norm_num)
  have hy : 2 ≤ Real.exp (L ^ (99 / 100 : ℝ)) := by
    linarith [Real.add_one_le_exp (L ^ (99 / 100 : ℝ))]
  have hm := abs_le.mp (hC (Real.exp (L ^ (99 / 100 : ℝ))) hy)
  rw [Real.log_exp, Real.log_rpow hLp] at hm
  constructor <;> linarith [Real.log_nonneg hL₁]

end TwoPointCorrelations

end OAI
