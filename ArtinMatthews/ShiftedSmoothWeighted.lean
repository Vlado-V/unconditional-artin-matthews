module

public import ArtinMatthews.ShiftedSmoothRankin
public import ArtinMatthews.ShiftedSmoothCount
public import Mathlib.Analysis.PSeries
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

/-! The weighted admissible common-prime-part count in the bilinear sum.
The only restriction on the small exponent is the convergence of its explicit
power series; the smooth-support count itself was proved by an Euler product.
-/

noncomputable section
open scoped BigOperators

namespace ArtinMatthews

theorem shiftedSmooth_weighted_count (α ε : ℝ) (hε : 0 < ε)
    (hα : ε < α - 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ,
      (∑ d ∈ Finset.Icc 1 B,
        ((shiftedSmoothSet B d.primeFactors).card : ℝ) * (d : ℝ)^(-α)) ≤
      C * (B : ℝ)^ε := by
  obtain ⟨C₀, hC₀, hcount⟩ := shiftedSmooth_count_subpower ε hε
  have hs : Summable (fun d : ℕ => (d : ℝ)^(ε-α)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  let Z : ℝ := ∑' d : ℕ, (d : ℝ)^(ε-α)
  have hZ : 0 ≤ Z := tsum_nonneg (fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _)
  refine ⟨C₀*(Z+1), mul_pos hC₀ (by linarith), ?_⟩
  intro B
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 B, C₀*(B : ℝ)^ε*(d : ℝ)^(ε-α) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hdreal : (0 : ℝ) < d := by exact_mod_cast hdpos
      calc
        _ ≤ (C₀*(B : ℝ)^ε*(d : ℝ)^ε) * (d : ℝ)^(-α) :=
          mul_le_mul_of_nonneg_right (hcount B d hdpos)
            (Real.rpow_nonneg hdreal.le _)
        _ = _ := by rw [mul_assoc, ← Real.rpow_add hdreal]; congr 2
    _ = (C₀*(B : ℝ)^ε) * ∑ d ∈ Finset.Icc 1 B, (d : ℝ)^(ε-α) := by
      rw [Finset.mul_sum]
    _ ≤ (C₀*(B : ℝ)^ε) * Z :=
      mul_le_mul_of_nonneg_left
        (hs.sum_le_tsum _ (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _))
        (mul_nonneg hC₀.le (Real.rpow_nonneg (Nat.cast_nonneg B) _))
    _ ≤ (C₀*(Z+1)) * (B : ℝ)^ε := by
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg B) ε]

end ArtinMatthews
