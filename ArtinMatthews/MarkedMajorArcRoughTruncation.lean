module

public import ArtinMatthews.MarkedMajorArcRoughCharacter
public import ArtinMatthews.MarkedBonferroniTail
public import ArtinMatthews.RoughBonferroniLayerBounds
public import ArtinMatthews.RoughBonferroniSupport
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual truncation remainder and divisor support in the real cutoff,
ready for the independent numerical logarithmic-depth estimates. -/
namespace ArtinMatthews
open Finset

 theorem marked_rough_truncation_error_bound (W C H u v : ℝ) (r : ℕ)
    (hW : 0 ≤ W) (hC : 0 ≤ C) (hH : 0 < H) (hv : 0 ≤ v) (hvH : v ≤ 2*H)
    (hrec : ∑ p ∈ Nat.primesLE ⌊W⌋₊, 1/(p:ℝ) ≤ C) :
    markedRoughTruncationError W r ⌊u⌋₊ ⌊v⌋₊/(H*markedSieveEulerProduct W) ≤
      2*markedFactorialTail C (r+1)/markedSieveEulerProduct W+
        W^(r+1)/(H*markedSieveEulerProduct W) := by
  have hV : 0 < markedSieveEulerProduct W := markedSieveEulerProduct_pos W
  have hlen : ((⌊v⌋₊-⌊u⌋₊:ℕ):ℝ) ≤ 2*H := by
    exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans ((Nat.floor_le hv).trans hvH)
  have hmass := rough_layer_reciprocal_mass_le_of_sum_le (Nat.primesLE ⌊W⌋₊) (r+1) hC hrec
  have hcard : (((Nat.primesLE ⌊W⌋₊).powersetCard (r+1)).card:ℝ) ≤ W^(r+1) := by
    have hc : (((Nat.primesLE ⌊W⌋₊).powersetCard (r+1)).card:ℝ) ≤ (⌊W⌋₊:ℝ)^(r+1) := by
      exact_mod_cast rough_layer_card_le_pow (Nat.primesLE ⌊W⌋₊) (r+1) ⌊W⌋₊
        (fun _ hp => Nat.prime_of_mem_primesLE hp) (fun _ hp => (Nat.mem_primesLE.mp hp).1)
    exact hc.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hW) (r+1))
  have htail : 0 ≤ markedFactorialTail C (r+1) := markedFactorialTail_nonneg hC _
  have hb : markedRoughTruncationError W r ⌊u⌋₊ ⌊v⌋₊ ≤
      2*H*markedFactorialTail C (r+1)+W^(r+1) := by
    unfold markedRoughTruncationError
    exact add_le_add (mul_le_mul hlen hmass (by positivity) (by positivity)) hcard
  calc
    _ ≤ (2*H*markedFactorialTail C (r+1)+W^(r+1))/(H*markedSieveEulerProduct W) :=
      div_le_div_of_nonneg_right hb (mul_pos hH hV).le
    _ = _ := by field_simp [hH.ne',hV.ne']

 theorem marked_rough_truncation_divisor_support {W : ℝ} (hW : 1 ≤ W)
    (r : ℕ) (D : Finset ℕ) (hD : D ∈ roughTruncationSubsets (Nat.primesLE ⌊W⌋₊) r) :
    0 < roughSubsetDivisor D ∧ (roughSubsetDivisor D:ℝ) ≤ W^(r+1) := by
  have hv : 1 ≤ ⌊W⌋₊ := (Nat.le_floor_iff (by linarith : 0≤W)).2 (by exact_mod_cast hW)
  obtain ⟨hd,_,hbound⟩ := roughTruncationSubsets_support (Nat.primesLE ⌊W⌋₊) r ⌊W⌋₊ hv
    (fun _ hp => Nat.prime_of_mem_primesLE hp) (fun _ hp => (Nat.mem_primesLE.mp hp).1) D hD
  refine ⟨hd,?_⟩
  have hh : (roughSubsetDivisor D:ℝ) ≤ (⌊W⌋₊:ℝ)^r := by exact_mod_cast hbound
  calc
    _ ≤ (⌊W⌋₊:ℝ)^r := hh
    _ ≤ W^r := pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) r
    _ ≤ W^(r+1) := by rw [pow_succ]; exact le_mul_of_one_le_right (by positivity) hW

end ArtinMatthews
