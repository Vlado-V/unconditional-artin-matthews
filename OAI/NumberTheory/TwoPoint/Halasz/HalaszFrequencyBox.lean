module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovMoment
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


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Explicit coordinate bounds for complete-system frequencies. -/
namespace TwoPointCorrelations

open Finset

lemma halasz_vinogradov_frequency_nonneg {s k M : ℕ} (x : Fin s → Fin M) (j : Fin k) :
    0≤halaszVinogradovFrequency k x j := by
  unfold halaszVinogradovFrequency
  exact sum_nonneg (fun _ _ => Int.natCast_nonneg _)

lemma halasz_vinogradov_frequency_le {s k M : ℕ} (x : Fin s → Fin M) (j : Fin k) :
    halaszVinogradovFrequency k x j≤(s*M^(j.val+1):ℕ) := by
  unfold halaszVinogradovFrequency
  have hh : (∑ i, ((x i).val+1)^(j.val+1))≤s*M^(j.val+1) := by
    calc
      _ ≤ ∑ _i : Fin s,M^(j.val+1) := sum_le_sum (fun i _ =>
        Nat.pow_le_pow_left (by omega : (x i).val+1≤M) _)
      _ = _ := by simp
  exact_mod_cast hh

lemma halasz_vinogradov_difference_abs {s k M : ℕ}
    (x y : Fin s → Fin M) (j : Fin k) :
    |halaszVinogradovFrequency k x j-halaszVinogradovFrequency k y j|≤
      (s*M^(j.val+1):ℕ) := by
  apply abs_le.mpr
  constructor <;> linarith [halasz_vinogradov_frequency_nonneg x j,
    halasz_vinogradov_frequency_nonneg y j,halasz_vinogradov_frequency_le x j,
    halasz_vinogradov_frequency_le y j]

end TwoPointCorrelations

end OAI
