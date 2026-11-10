module

public import ArtinMatthews.CubicThetaCoefficients
public import ArtinMatthews.QuadraticIdealNormCountGlobal
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.Jacobsthal.Sieve.DivisorLogGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform subpower growth and global mean-square bounds for the actual
Eisenstein ideal-theta coefficients. -/

noncomputable section
open scoped BigOperators

namespace ArtinMatthews

open OAI.SevenEighths

/-- Every fixed natural power of the actual coefficients has a subpower bound,
uniformly over the genuine residue characters. -/
theorem idealThetaCoeff_power_subpower (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeFamily.Character) (n : ℕ), 1 ≤ n →
      ‖idealThetaCoeff χ n‖ ^ k ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, hdiv⟩ :=
    OAI.Erdos970.ErdosDivisorBounds.divisor_power_subpower k hε
  refine ⟨C, hC, ?_⟩
  intro χ n hn
  exact (pow_le_pow_left₀ (norm_nonneg _) (idealThetaCoeff_norm_le_divisors_card χ n) k).trans
    (hdiv n hn)

/-- Pointwise subpower coefficient growth, with a constant independent of the
character and of the positive index. -/
theorem idealThetaCoeff_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeFamily.Character) (n : ℕ), 1 ≤ n →
      ‖idealThetaCoeff χ n‖ ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := idealThetaCoeff_power_subpower 1 ε hε
  refine ⟨C, hC, ?_⟩
  intro χ n hn
  simpa only [pow_one] using h χ n hn

/-- The squared coefficient estimate also holds at zero, because the actual
zero coefficient vanishes. -/
theorem idealThetaCoeff_square_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeFamily.Character) (n : ℕ),
      ‖idealThetaCoeff χ n‖ ^ 2 ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := idealThetaCoeff_power_subpower 2 ε hε
  refine ⟨C, hC, ?_⟩
  intro χ n
  by_cases hn : n = 0
  · simp only [hn, idealThetaCoeff_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity
  exact h χ n (Nat.one_le_iff_ne_zero.mpr hn)

/-- Mean square over any finite index family of at most `N` terms, all bounded
by `N`. The same constant works for every actual character and every family. -/
theorem idealThetaCoeff_meanSquare_finset (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeFamily.Character) (N : ℕ) (s : Finset ℕ),
      s.card ≤ N → (∀ n ∈ s, n ≤ N) →
      (∑ n ∈ s, ‖idealThetaCoeff χ n‖ ^ 2) ≤ C * (N : ℝ) ^ (1 + ε) := by
  obtain ⟨C, hC, hbound⟩ := idealThetaCoeff_square_subpower ε hε
  refine ⟨C, hC, ?_⟩
  intro χ N s hcard hindex
  by_cases hN : N = 0
  · have hs : s = ∅ := Finset.card_eq_zero.mp (by omega)
    simp only [hs, Finset.sum_empty]
    positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  calc
    _ ≤ ∑ _n ∈ s, C * (N : ℝ) ^ ε := by
      apply Finset.sum_le_sum
      intro n hn
      exact (hbound χ n).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hindex n hn) hε.le) hC.le)
    _ = (s.card : ℝ) * (C * (N : ℝ) ^ ε) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (C * (N : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = C * (N : ℝ) ^ (1 + ε) := by
      rw [Real.rpow_add hNpos, Real.rpow_one]
      ring

/-- Global mean square with the natural `range N` convention. -/
theorem idealThetaCoeff_meanSquare_range (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeFamily.Character) (N : ℕ),
      (∑ n ∈ Finset.range N, ‖idealThetaCoeff χ n‖ ^ 2) ≤
        C * (N : ℝ) ^ (1 + ε) := by
  obtain ⟨C, hC, h⟩ := idealThetaCoeff_meanSquare_finset ε hε
  refine ⟨C, hC, ?_⟩
  intro χ N
  exact h χ N (Finset.range N) (by simp)
    (fun n hn => (Finset.mem_range.mp hn).le)

/-- Global mean square over the positive indices at most `N`. -/
theorem idealThetaCoeff_meanSquare_Icc (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeFamily.Character) (N : ℕ),
      (∑ n ∈ Finset.Icc 1 N, ‖idealThetaCoeff χ n‖ ^ 2) ≤
        C * (N : ℝ) ^ (1 + ε) := by
  obtain ⟨C, hC, h⟩ := idealThetaCoeff_meanSquare_finset ε hε
  refine ⟨C, hC, ?_⟩
  intro χ N
  exact h χ N (Finset.Icc 1 N) (by simp [Nat.card_Icc])
    (fun _ hn => (Finset.mem_Icc.mp hn).2)

/-- The real-cutoff global mean-square estimate, uniformly in the actual
character. The positive indices are precisely those at most `⌊X⌋₊`. -/
theorem idealThetaCoeff_meanSquare_real (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeFamily.Character) (X : ℝ), 0 ≤ X →
      (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ‖idealThetaCoeff χ n‖ ^ 2) ≤
        C * X ^ (1 + ε) := by
  obtain ⟨C, hC, h⟩ := idealThetaCoeff_meanSquare_Icc ε hε
  refine ⟨C, hC, ?_⟩
  intro χ X hX
  exact (h χ ⌊X⌋₊).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hX) (by positivity)) hC.le)

end ArtinMatthews
