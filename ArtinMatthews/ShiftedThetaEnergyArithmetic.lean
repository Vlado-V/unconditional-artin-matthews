module

public import ArtinMatthews.CubicThetaCoefficients
public import ArtinMatthews.ShiftedCommonPrimePartSquarefree
public import ArtinMatthews.CubicThetaDiagonal
public import ArtinMatthews.ShiftedOffDiagonalArithmetic
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

/-! One constant controls the actual diagonal and both off-diagonal
arithmetic weights, uniformly over the coefficient character. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

private theorem shiftedBand_subset {M : ℕ} (hM : 0 < M) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc M (2*M)) : A ⊆ Finset.Icc 1 (2*M) := by
  intro m hm
  rcases Finset.mem_Icc.mp (hA hm) with ⟨hlo,hhi⟩
  exact Finset.mem_Icc.mpr ⟨(Nat.succ_le_iff.mpr hM).trans hlo,hhi⟩

private theorem shiftedBand_offDiag_subset {M : ℕ} (hM : 0 < M) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc M (2*M)) : A.offDiag ⊆ shiftedSourcePairs (2*M) := by
  intro p hp
  rcases Finset.mem_offDiag.mp hp with ⟨h1,h2,hne⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨shiftedBand_subset hM A hA h1, shiftedBand_subset hM A hA h2⟩,hne⟩

theorem shiftedTheta_energy_arithmetic (δ : ℝ) (hδ : 0 < δ) (hsmall : δ < 1/2) :
    ∃ K : ℝ, 0 < K ∧
      (∀ (χ : OAI.SevenEighths.HeckeFamily.Character) (M : ℕ) (T : ℝ) (A : Finset ℕ),
        0 < M → 1 ≤ T → A ⊆ Finset.Icc M (2*M) →
        (∑ m ∈ A, ∑ n ∈ Finset.Icc 1 ⌈2*T⌉₊, ‖idealThetaCoeff χ (m*n+1)‖^2) ≤
          K * (6*(M : ℝ)*T+1)^(1+δ)) ∧
      (∀ (M : ℕ) (A : Finset ℕ), 0 < M → A ⊆ Finset.Icc M (2*M) →
        (∑ p ∈ A.offDiag,
          (shiftedCommonPrimePart p.1 p.2 : ℝ) / Real.sqrt (p.1.gcd p.2)) ≤
          K * (2*(M : ℝ))^(2+δ)) ∧
      (∀ (M : ℕ) (A : Finset ℕ), 0 < M → A ⊆ Finset.Icc M (2*M) →
        (∑ p ∈ A.offDiag, (shiftedCommonPrimePart p.1 p.2 : ℝ)^(1/4 : ℝ)) ≤
          K * (2*(M : ℝ))^(2+δ)) := by
  obtain ⟨Kd,hKd,hdiag⟩ := idealTheta_diagonal_subpower δ hδ
  obtain ⟨K1,hK1,hfirst⟩ := shiftedOffDiagonal_first_weight δ hδ hsmall
  obtain ⟨K2,hK2,hsecond⟩ := shiftedOffDiagonal_second_weight δ hδ (by linarith)
  let K := Kd + K1 + K2
  have hK : 0 < K := by dsimp only [K]; positivity
  have hdK : Kd ≤ K := by dsimp only [K]; linarith
  have h1K : K1 ≤ K := by dsimp only [K]; linarith
  have h2K : K2 ≤ K := by dsimp only [K]; linarith
  refine ⟨K,hK,?_,?_,?_⟩
  · intro χ M T A hM hT hA
    have hceil : (⌈2*T⌉₊ : ℝ) ≤ 3*T := by
      have h := Nat.ceil_lt_add_one (by linarith : 0 ≤ 2*T)
      linarith
    have hscale : (((2*M)*⌈2*T⌉₊+1 : ℕ) : ℝ) ≤ 6*(M : ℝ)*T+1 := by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 (2*M), ∑ n ∈ Finset.Icc 1 ⌈2*T⌉₊,
          ‖idealThetaCoeff χ (m*n+1)‖^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (shiftedBand_subset hM A hA)
          (fun m _ _ => Finset.sum_nonneg (fun n _ => sq_nonneg _))
      _ ≤ Kd * (((2*M)*⌈2*T⌉₊+1 : ℕ) : ℝ)^(1+δ) := hdiag χ (2*M) ⌈2*T⌉₊
      _ ≤ K * (((2*M)*⌈2*T⌉₊+1 : ℕ) : ℝ)^(1+δ) :=
        mul_le_mul_of_nonneg_right hdK (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hscale (by positivity)) hK.le
  · intro M A hM hA
    calc
      _ ≤ ∑ p ∈ shiftedSourcePairs (2*M),
          (shiftedCommonPrimePart p.1 p.2 : ℝ) / Real.sqrt (p.1.gcd p.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (shiftedBand_offDiag_subset hM A hA)
          (fun p _ _ => div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
      _ ≤ K1 * ((2*M : ℕ) : ℝ)^(2+δ) := hfirst (2*M)
      _ ≤ _ := by
        push_cast
        exact mul_le_mul_of_nonneg_right h1K (Real.rpow_nonneg (by positivity) _)
  · intro M A hM hA
    calc
      _ ≤ ∑ p ∈ shiftedSourcePairs (2*M),
          (shiftedCommonPrimePart p.1 p.2 : ℝ)^(1/4 : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (shiftedBand_offDiag_subset hM A hA)
          (fun p _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ K2 * ((2*M : ℕ) : ℝ)^(2+δ) := hsecond (2*M)
      _ ≤ _ := by
        push_cast
        exact mul_le_mul_of_nonneg_right h2K (Real.rpow_nonneg (by positivity) _)

end
end ArtinMatthews
