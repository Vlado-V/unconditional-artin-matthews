module

public import ArtinMatthews.MarkedBonferroniTail
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

/-! Fixed represented-label multiplicities and the union-count prefactor
fit the factorial tail at the original omitted depth. -/

noncomputable section
namespace ArtinMatthews

theorem cubicSampling_tail_factorial_envelope (K h : ℕ) (hh : 0 < h) {B : ℝ}
    (hB : 0 ≤ B) :
    let D := 2 * h + 2 * K
    ((D + 1 : ℕ) : ℝ) * (D : ℝ) ^ (2 * K) * B ^ D / (h.factorial : ℝ) ≤
      ((2 * K + 3 : ℕ) : ℝ) ^ (2 * K + 1) * B ^ (2 * K) *
        markedFactorialTail ((2 : ℝ) ^ (2 * K + 1) * B ^ 2) h := by
  dsimp only
  let D := 2 * h + 2 * K
  let s := 2 * K
  have hmul : 2 * K + 1 ≤ (2 * K + 1) * h := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 * K + 1) hh
  have hD : D + 1 ≤ (2 * K + 3) * h := by
    rw [show (2 * K + 3) * h = 2 * h + (2 * K + 1) * h by ring]
    dsimp only [D]
    omega
  have hpowD : D + 1 ≤ (2 * K + 3) * 2 ^ h :=
    hD.trans (Nat.mul_le_mul_left _ Nat.lt_two_pow_self.le)
  have hnat : (D + 1) * D ^ s ≤ ((2 * K + 3) * 2 ^ h) ^ (s + 1) := by
    calc
      _ ≤ (D + 1) * (D + 1) ^ s := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) _)
      _ = (D + 1) ^ (s + 1) := (pow_succ' _ _).symm
      _ ≤ _ := Nat.pow_le_pow_left hpowD _
  have hreal : ((D + 1 : ℕ) : ℝ) * (D : ℝ) ^ s ≤
      ((2 * K + 3 : ℕ) : ℝ) ^ (s + 1) * (((2 : ℝ) ^ (s + 1)) ^ h) := by
    calc
      _ ≤ ((((2 * K + 3) * 2 ^ h : ℕ) : ℝ)) ^ (s + 1) := by exact_mod_cast hnat
      _ = _ := by
        push_cast
        rw [mul_pow, ← pow_mul, Nat.mul_comm h (s + 1), pow_mul]
  have hBpow : B ^ D = B ^ s * (B ^ 2) ^ h := by
    dsimp only [D, s]
    rw [pow_add, pow_mul]
    ring
  change ((D + 1 : ℕ) : ℝ) * (D : ℝ) ^ s * B ^ D / (h.factorial : ℝ) ≤ _
  calc
    _ ≤ (((2 * K + 3 : ℕ) : ℝ) ^ (s + 1) * (((2 : ℝ) ^ (s + 1)) ^ h)) *
        B ^ D / (h.factorial : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hreal (pow_nonneg hB _))
        (Nat.cast_nonneg _)
    _ = _ := by
      rw [hBpow]
      simp only [markedFactorialTail, mul_pow]
      dsimp only [s]
      ring

end ArtinMatthews
