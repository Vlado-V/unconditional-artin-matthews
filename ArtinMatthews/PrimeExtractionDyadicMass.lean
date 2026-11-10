module

public import ArtinMatthews.PrimeExtractionDyadicSupport
public import ArtinMatthews.PrimeExtractionMellinBilinear
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

/-! Each retained dyadic box has coefficient mass of order the product
cutoff, even when Mellin separation has removed the cutoff itself. -/

namespace ArtinMatthews
open scoped BigOperators

theorem primeExtractionDyadicBox_card_le (N k l : ℕ) :
    (primeExtractionDyadicBlock N k).card * (primeExtractionDyadicBlock N l).card ≤
      2^k * 2^l :=
  Nat.mul_le_mul (primeExtractionDyadicBlock_card_le N k) (primeExtractionDyadicBlock_card_le N l)

theorem primeExtractionDyadicBox_mass_le {N k l : ℕ} (A : ℕ → ℕ → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hactive : 2^k * 2^l ≤ N)
    (hA : ∀ m ∈ primeExtractionDyadicBlock N k,
      ∀ n ∈ primeExtractionDyadicBlock N l, ‖A m n‖ ≤ C) :
    primeExtractionBilinearMass (primeExtractionDyadicBlock N k)
      (primeExtractionDyadicBlock N l) A ≤ C*N := by
  have hcard : (((primeExtractionDyadicBlock N k).card *
      (primeExtractionDyadicBlock N l).card : ℕ) : ℝ) ≤ N := by
    exact_mod_cast (primeExtractionDyadicBox_card_le N k l).trans hactive
  unfold primeExtractionBilinearMass
  calc
    _ ≤ ∑ _m ∈ primeExtractionDyadicBlock N k, ∑ _n ∈ primeExtractionDyadicBlock N l, C :=
      Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (hA m hm))
    _ = (((primeExtractionDyadicBlock N k).card *
        (primeExtractionDyadicBlock N l).card : ℕ) : ℝ) * C := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_mul]
      ring
    _ ≤ (N : ℝ)*C := mul_le_mul_of_nonneg_right hcard hC
    _ = _ := mul_comm _ _

theorem primeExtractionDyadicActive_mass_le {N : ℕ} {kl : ℕ × ℕ}
    (hkl : kl ∈ primeExtractionDyadicActive N) (A : ℕ → ℕ → ℂ)
    {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ m ∈ primeExtractionDyadicBlock N kl.1,
      ∀ n ∈ primeExtractionDyadicBlock N kl.2, ‖A m n‖ ≤ C) :
    primeExtractionBilinearMass (primeExtractionDyadicBlock N kl.1)
      (primeExtractionDyadicBlock N kl.2) A ≤ C*N :=
  primeExtractionDyadicBox_mass_le A hC (Finset.mem_filter.mp hkl).2 hA

/-- The sum of all box masses costs only the square-logarithmic number
of retained boxes, rather than the area of the original rectangle. -/
theorem primeExtractionDyadicTotal_mass_le (N : ℕ) (A : ℕ → ℕ → ℂ)
    {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ kl ∈ primeExtractionDyadicActive N, ∀ m ∈ primeExtractionDyadicBlock N kl.1,
      ∀ n ∈ primeExtractionDyadicBlock N kl.2, ‖A m n‖ ≤ C) :
    (∑ kl ∈ primeExtractionDyadicActive N,
      primeExtractionBilinearMass (primeExtractionDyadicBlock N kl.1)
        (primeExtractionDyadicBlock N kl.2) A) ≤
      C*N*(1+Real.log (N+1)/Real.log 2)^2 := by
  calc
    _ ≤ ∑ _kl ∈ primeExtractionDyadicActive N, C*(N : ℝ) :=
      Finset.sum_le_sum (fun kl hkl => primeExtractionDyadicActive_mass_le hkl A hC (hA kl hkl))
    _ = C*N*((primeExtractionDyadicActive N).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (primeExtractionDyadicActive_count_le N)
      (mul_nonneg hC (Nat.cast_nonneg N))

theorem primeExtractionDyadicActive_mass_le_scale {N : ℕ} {kl : ℕ × ℕ}
    (hkl : kl ∈ primeExtractionDyadicActive N) (A : ℕ → ℕ → ℂ)
    {C T x : ℝ} (hC : 0 ≤ C) (hN : (N : ℝ) ≤ T*x)
    (hA : ∀ m ∈ primeExtractionDyadicBlock N kl.1,
      ∀ n ∈ primeExtractionDyadicBlock N kl.2, ‖A m n‖ ≤ C) :
    primeExtractionBilinearMass (primeExtractionDyadicBlock N kl.1)
      (primeExtractionDyadicBlock N kl.2) A ≤ C*T*x :=
  (primeExtractionDyadicActive_mass_le hkl A hC hA).trans
    ((mul_le_mul_of_nonneg_left hN hC).trans_eq (by ring))

end ArtinMatthews
