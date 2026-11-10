module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Rat.Defs
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Translation and dilation preserve the complete Vinogradov system.
These are the finite identities used before averaging its solutions. -/
namespace TwoPointCorrelations

open Finset

theorem halasz_vinogradov_translate {s k : ℕ} (x y : Fin s → ℚ)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, x i^j = ∑ i, y i^j)
    (c : ℚ) : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i, (x i+c)^j = ∑ i, (y i+c)^j := by
  intro j _hj hjk
  have hbinom (z : Fin s → ℚ) :
      (∑ i, (z i+c)^j) = ∑ m ∈ range (j+1),
        (∑ i, z i^m)*c^(j-m)*(Nat.choose j m:ℚ) := by
    simp only [add_pow]
    rw [sum_comm]
    apply sum_congr rfl
    intro m _
    rw [← sum_mul,← sum_mul]
  rw [hbinom,hbinom]
  apply sum_congr rfl
  intro m hm
  have hmj : m ≤ j := by have := mem_range.mp hm; omega
  have he : (∑ i, x i^m) = ∑ i, y i^m := by
    by_cases hz : m=0
    · simp [hz]
    · exact hpower m (by omega) (hmj.trans hjk)
  rw [he]

theorem halasz_vinogradov_dilate {s k : ℕ} (x y : Fin s → ℚ)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, x i^j = ∑ i, y i^j)
    (a : ℚ) : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i, (a*x i)^j = ∑ i, (a*y i)^j := by
  intro j hj hjk
  simp only [mul_pow,← mul_sum]
  rw [hpower j hj hjk]

theorem halasz_vinogradov_affine {s k : ℕ} (x y : Fin s → ℚ)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, x i^j = ∑ i, y i^j)
    (a c : ℚ) : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i, (a*x i+c)^j = ∑ i, (a*y i+c)^j :=
  halasz_vinogradov_translate _ _ (halasz_vinogradov_dilate x y hpower a) c

end TwoPointCorrelations

end OAI
