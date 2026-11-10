module

public import ArtinMatthews.ShiftedBilinearMajorant
public import ArtinMatthews.ShiftedDyadicFiniteBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite domination by the two fixed smooth bumps. -/
namespace ArtinMatthews
open Set
open scoped BigOperators
noncomputable section

theorem shiftedDyadic_supported_sum_le (S : ℝ) (B : Finset ℕ) (g : ℝ → ℝ) (F : ℕ → ℝ)
    (hB : ∀ n ∈ B, 1 ≤ n) (hg : ∀ x, 0 ≤ g x)
    (hs : Function.support g ⊆ Icc S (2 * S)) (hF : ∀ n, 0 ≤ F n) :
    (∑ n ∈ B, g n * F n) ≤ ∑ n ∈ Finset.Icc 1 ⌈2 * S⌉₊, g n * F n := by
  let U := Finset.Icc 1 ⌈2 * S⌉₊
  have hzero (n : ℕ) (hn : n ∈ B) (hout : n ∉ U) : g n * F n = 0 := by
    by_cases hz : g n = 0
    · rw [hz, zero_mul]
    have hsupport := hs hz
    have hu : n ∈ U := by
      apply Finset.mem_Icc.mpr
      refine ⟨hB n hn, ?_⟩
      exact_mod_cast hsupport.2.trans (Nat.le_ceil (2 * S))
    exact False.elim (hout hu)
  have he : (∑ n ∈ B ∩ U, g n * F n) = ∑ n ∈ B, g n * F n := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro n hn hout
    apply hzero n hn
    intro hu
    exact hout (Finset.mem_inter.mpr ⟨hn, hu⟩)
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    (fun n _ _ => mul_nonneg (hg n) (hF n))

theorem shiftedDyadic_twoBump_sum (T : ℕ) (hT : 2 ≤ T) (B : Finset ℕ)
    (hB : B ⊆ Finset.Icc T (2 * T)) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    (∑ n ∈ B, F n) ≤
      (∑ n ∈ Finset.Icc 1 ⌈2 * shiftedBilinearMajorantScale1 T⌉₊,
        (shiftedBilinearScaledBump (shiftedBilinearMajorantScale1 T) n).re * F n) +
      (∑ n ∈ Finset.Icc 1 ⌈2 * shiftedBilinearMajorantScale2 T⌉₊,
        (shiftedBilinearScaledBump (shiftedBilinearMajorantScale2 T) n).re * F n) := by
  have hTreal : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hTp : (0 : ℝ) < T := lt_of_lt_of_le (by norm_num) hTreal
  have hBn (n : ℕ) (hn : n ∈ B) : 1 ≤ n := by
    have h := (Finset.mem_Icc.mp (hB hn)).1
    omega
  have hscaled := shiftedBilinearMajorant_scales T hTreal
  have hs1 : 0 < shiftedBilinearMajorantScale1 T := lt_of_lt_of_le zero_lt_one hscaled.1
  have hs2 : 0 < shiftedBilinearMajorantScale2 T := lt_of_lt_of_le zero_lt_one hscaled.2.1
  calc
    _ ≤ ∑ n ∈ B, shiftedBilinearMajorant T n * F n := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' : (n : ℝ) ∈ Icc (T : ℝ) (2 * T) := by
        have h := Finset.mem_Icc.mp (hB hn)
        exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (shiftedBilinearMajorant_ge_one T n hTp hn') (hF n)
    _ = (∑ n ∈ B, (shiftedBilinearScaledBump (shiftedBilinearMajorantScale1 T) n).re * F n) +
        ∑ n ∈ B, (shiftedBilinearScaledBump (shiftedBilinearMajorantScale2 T) n).re * F n := by
      simp only [shiftedBilinearMajorant, add_mul, Finset.sum_add_distrib]
    _ ≤ _ := add_le_add
      (shiftedDyadic_supported_sum_le _ B _ F hBn
        (fun x => (shiftedBilinearScaledBump_re_bounds _ x).1)
        (shiftedBilinearScaledBump_re_support _ hs1) hF)
      (shiftedDyadic_supported_sum_le _ B _ F hBn
        (fun x => (shiftedBilinearScaledBump_re_bounds _ x).1)
        (shiftedBilinearScaledBump_re_support _ hs2) hF)

theorem shiftedDyadic_twoBump_cauchy (T : ℕ) (hT : 2 ≤ T) (A B : Finset ℕ)
    (hB : B ⊆ Finset.Icc T (2 * T)) (α β : ℕ → ℂ) (K : ℕ → ℕ → ℂ)
    (hβ : ∀ n ∈ B, ‖β n‖ ≤ 1) :
    ‖∑ m ∈ A, ∑ n ∈ B, α m * β n * K m n‖ ^ 2 ≤
      2 * (T : ℝ) *
      ((∑ n ∈ Finset.Icc 1 ⌈2 * shiftedBilinearMajorantScale1 T⌉₊,
        (shiftedBilinearScaledBump (shiftedBilinearMajorantScale1 T) n).re *
          ‖∑ m ∈ A, α m * K m n‖ ^ 2) +
      (∑ n ∈ Finset.Icc 1 ⌈2 * shiftedBilinearMajorantScale2 T⌉₊,
        (shiftedBilinearScaledBump (shiftedBilinearMajorantScale2 T) n).re *
          ‖∑ m ∈ A, α m * K m n‖ ^ 2)) := by
  calc
    _ ≤ (B.card : ℝ) * ∑ n ∈ B, ‖∑ m ∈ A, α m * K m n‖ ^ 2 :=
      shiftedDyadic_bilinear_cauchy A B α β K hβ
    _ ≤ 2 * (T : ℝ) * ∑ n ∈ B, ‖∑ m ∈ A, α m * K m n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (shiftedDyadic_card_le T (by omega) B hB)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (shiftedDyadic_twoBump_sum T hT B hB _ (fun _ => sq_nonneg _))
      (by positivity)

end
end ArtinMatthews
