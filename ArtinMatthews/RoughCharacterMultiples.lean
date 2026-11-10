module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import ArtinMatthews.MarkedMajorArcDivisorReindex
public import ArtinMatthews.RoughBonferroniInterval
public import ArtinMatthews.RoughCharacterPeriod
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

/-! Literal interval divisibility counts and actual character sums along
multiples, with explicit finite endpoint errors. -/
noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators Classical

theorem rough_quotient_discrepancy_le (N d : ℕ) (hd : 0 < d) :
    |((N / d : ℕ) : ℝ) - (N : ℝ) / d| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmod : ((N % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt N hd
  have he : (N : ℝ) = ((N / d : ℕ) : ℝ) * d + (N % d : ℕ) := by
    exact_mod_cast (show N = N / d * d + N % d by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod N d).symm)
  have hrem : (0 : ℝ) ≤ (N % d : ℕ) := Nat.cast_nonneg _
  have hlo : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 :=
    (div_lt_iff₀ hdR).mpr (by nlinarith)
  have hhi : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d :=
    (le_div_iff₀ hdR).mpr (by nlinarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Two endpoints give an absolute error at most two. -/
theorem rough_interval_multiples_discrepancy_le (M N d : ℕ) (hd : 0 < d) :
    |(∑ n ∈ Ioc M N, if d ∣ n then (1 : ℝ) else 0) -
      ((N - M : ℕ) : ℝ) / d| ≤ 2 := by
  rw [rough_interval_multiples_sum M N d hd]
  by_cases hMN : M ≤ N
  · rw [Nat.cast_sub (Nat.div_le_div_right hMN), Nat.cast_sub hMN]
    have he : (((N / d : ℕ) : ℝ) - (M / d : ℕ)) - ((N : ℝ) - M) / d =
        (((N / d : ℕ) : ℝ) - (N : ℝ) / d) -
          (((M / d : ℕ) : ℝ) - (M : ℝ) / d) := by ring
    rw [he]
    calc
      _ ≤ |((N / d : ℕ) : ℝ) - (N : ℝ) / d| +
          |((M / d : ℕ) : ℝ) - (M : ℝ) / d| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (((N / d : ℕ) : ℝ) - (N : ℝ) / d) 0
            (((M / d : ℕ) : ℝ) - (M : ℝ) / d)
      _ ≤ 1 + 1 := add_le_add (rough_quotient_discrepancy_le N d hd)
        (rough_quotient_discrepancy_le M d hd)
      _ = 2 := by norm_num
  · have hNM : N ≤ M := by omega
    rw [Nat.sub_eq_zero_of_le (Nat.div_le_div_right hNM), Nat.sub_eq_zero_of_le hNM]
    norm_num

theorem rough_character_multiples_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (M N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Ioc M N, if d ∣ n then χ (n : ZMod q) else 0) =
      χ (d : ZMod q) * ∑ n ∈ Ioc (M / d) (N / d), χ (n : ZMod q) := by
  rw [marked_sum_Ioc_dvd_reindex hd, mul_sum]
  apply sum_congr rfl
  intro n _
  simp only [Nat.cast_mul, map_mul]

theorem rough_nonprincipal_character_multiples_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M N d : ℕ) (hd : 0 < d) :
    ‖∑ n ∈ Ioc M N, if d ∣ n then χ (n : ZMod q) else 0‖ ≤ (q : ℝ) := by
  rw [rough_character_multiples_sum χ M N d hd, norm_mul]
  exact (mul_le_mul (χ.norm_le_one _) (rough_nonprincipal_character_Ioc_norm_le χ hχ _ _)
    (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

end ArtinMatthews
