module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Complex.Norm
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Combining uniform prefix bounds on dyadic blocks. -/
namespace TwoPointCorrelations

open Finset

theorem halasz_dyadic_prefix (f : ℕ → ℂ) {B : ℝ} (hB : 0≤B)
    (hzero : ‖f 0‖≤B)
    (K : ℕ) (hblock : ∀ k<K, ∀ H : ℕ, H≤2^k → ‖∑ i∈range H,f (2^k+i)‖≤B) :
    ∀ M : ℕ, M≤2^K → ‖∑ n∈range M,f n‖≤((K:ℝ)+1)*B := by
  induction K with
  | zero =>
    intro M hM
    have hM1 : M≤1 := by simpa only [pow_zero] using hM
    interval_cases M
    · simpa using hB
    · simpa using hzero
  | succ K ih =>
    have hprev : ∀ k<K, ∀ H : ℕ, H≤2^k → ‖∑ i∈range H,f (2^k+i)‖≤B :=
      fun k hk H hH => hblock k (by omega) H hH
    intro M hM
    by_cases hsmall : M≤2^K
    · have hh := ih hprev M hsmall
      push_cast
      linarith
    · have hsplit : M=2^K+(M-2^K) := by omega
      have htail : M-2^K≤2^K := by rw [pow_succ] at hM; omega
      conv_lhs => rw [hsplit, sum_range_add]
      apply (norm_add_le _ _).trans
      have hleft := ih hprev (2^K) le_rfl
      have hright := hblock K (by omega) (M-2^K) htail
      push_cast
      linarith

end TwoPointCorrelations

end OAI
