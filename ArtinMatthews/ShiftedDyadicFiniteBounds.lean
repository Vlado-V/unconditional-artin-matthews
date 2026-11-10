module

public import ArtinMatthews.CubicThetaCoefficients
public import ArtinMatthews.CubicThetaMeanSquare
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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

/-! Finite counting, Cauchy--Schwarz, and the actual theta divisor majorant. -/
namespace ArtinMatthews
open OAI.SevenEighths
open scoped BigOperators
noncomputable section

theorem shiftedDyadic_card_le (M : ℕ) (hM : 0 < M) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc M (2 * M)) : (A.card : ℝ) ≤ 2 * (M : ℝ) := by
  have h := Finset.card_le_card hA
  rw [Nat.card_Icc] at h
  have hcard : A.card ≤ 2 * M := by omega
  exact_mod_cast hcard

theorem shiftedDyadic_bilinear_cauchy (A B : Finset ℕ) (α β : ℕ → ℂ)
    (K : ℕ → ℕ → ℂ) (hβ : ∀ n ∈ B, ‖β n‖ ≤ 1) :
    ‖∑ m ∈ A, ∑ n ∈ B, α m * β n * K m n‖ ^ 2 ≤
      (B.card : ℝ) * ∑ n ∈ B, ‖∑ m ∈ A, α m * K m n‖ ^ 2 := by
  have he : (∑ m ∈ A, ∑ n ∈ B, α m * β n * K m n) =
      ∑ n ∈ B, β n * ∑ m ∈ A, α m * K m n := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [he]
  have hnorm : ‖∑ n ∈ B, β n * ∑ m ∈ A, α m * K m n‖ ≤
      ∑ n ∈ B, ‖∑ m ∈ A, α m * K m n‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hβ n hn) (norm_nonneg _)).trans_eq (one_mul _)
  exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
    hnorm).trans (sq_sum_le_card_mul_sum_sq)

theorem shiftedDyadic_theta_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : HeckeFamily.Character) (M T : ℕ), 0 < M → 0 < T →
      ∀ (A B : Finset ℕ), A ⊆ Finset.Icc M (2 * M) → B ⊆ Finset.Icc T (2 * T) →
      ∀ (α β : ℕ → ℂ), (∀ m ∈ A, ‖α m‖ ≤ 1) → (∀ n ∈ B, ‖β n‖ ≤ 1) →
      ‖∑ m ∈ A, ∑ n ∈ B, α m * β n * idealThetaCoeff η (m * n + 1)‖ ≤
        C * ((M : ℝ) * T) ^ ε * ((M : ℝ) * T) := by
  obtain ⟨C, hC, htheta⟩ := idealThetaCoeff_subpower ε hε
  refine ⟨4 * C * (5 : ℝ) ^ ε, by positivity, ?_⟩
  intro η M T hM hT A B hA hB α β hα hβ
  have hMT : 1 ≤ M * T := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.ne_of_gt hM) (Nat.ne_of_gt hT))
  have hMT0 : 0 ≤ (M : ℝ) * T := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbound (m : ℕ) (hm : m ∈ A) (n : ℕ) (hn : n ∈ B) :
      ‖idealThetaCoeff η (m * n + 1)‖ ≤ C * (5 * ((M : ℝ) * T)) ^ ε := by
    have hm' := (Finset.mem_Icc.mp (hA hm)).2
    have hn' := (Finset.mem_Icc.mp (hB hn)).2
    have hproduct := Nat.mul_le_mul hm' hn'
    have hindex : m * n + 1 ≤ 5 * (M * T) := by nlinarith
    exact (htheta η (m * n + 1) (by omega)).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hindex) hε.le) hC.le)
  have hterm (m : ℕ) (hm : m ∈ A) (n : ℕ) (hn : n ∈ B) :
      ‖α m * β n * idealThetaCoeff η (m * n + 1)‖ ≤ C * (5 * ((M : ℝ) * T)) ^ ε := by
    rw [norm_mul, norm_mul]
    simpa only [one_mul, mul_one] using
      (mul_le_mul (mul_le_mul (hα m hm) (hβ n hn) (norm_nonneg _) (by norm_num))
        (hbound m hm n hn) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1))
  have hcard : (A.card : ℝ) * B.card ≤ (2 * (M : ℝ)) * (2 * (T : ℝ)) :=
    mul_le_mul (shiftedDyadic_card_le M hM A hA) (shiftedDyadic_card_le T hT B hB)
      (Nat.cast_nonneg _) (by positivity)
  calc
    _ ≤ ∑ m ∈ A, ∑ n ∈ B, ‖α m * β n * idealThetaCoeff η (m * n + 1)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ => norm_sum_le _ _))
    _ ≤ ∑ _m ∈ A, ∑ _n ∈ B, C * (5 * ((M : ℝ) * T)) ^ ε :=
      Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun n hn => hterm m hm n hn))
    _ = ((A.card : ℝ) * B.card) * (C * (5 * ((M : ℝ) * T)) ^ ε) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ((2 * (M : ℝ)) * (2 * (T : ℝ))) * (C * (5 * ((M : ℝ) * T)) ^ ε) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))
    _ = (4 * C * (5 : ℝ) ^ ε) * ((M : ℝ) * T) ^ ε * ((M : ℝ) * T) := by
      rw [Real.mul_rpow (by norm_num) hMT0]
      ring

end
end ArtinMatthews
