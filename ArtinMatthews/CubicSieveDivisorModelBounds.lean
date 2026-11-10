module

public import ArtinMatthews.CubicSieveDivisorModelNormalized
public import ArtinMatthews.CubicSieveBlockHarmonic
public import ArtinMatthews.CubicSieveDivisorBlockBounds
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The genuine Section 7.1 overflow model at one and its first derivative. -/

noncomputable section
namespace ArtinMatthews

open Finset Filter
open scoped BigOperators Topology

theorem cubicSieve_divisorModel_normalized_value_bound {z A : ℝ} (hz : 1 < z) (hA : 0 ≤ A)
    {m : ℕ} (hm : 1 ≤ m)
    (hmass : ∀ j, (∑ p ∈ cubicSieveBlock z j, cubicSievePrimeDivisorDensity p) ≤ A) :
    let C := Real.exp (12 * A)
    0 ≤ cubicSieveDivisorCorrectionModel z m 1 / markedSieveEulerProduct z ^ 2 ∧
      cubicSieveDivisorCorrectionModel z m 1 / markedSieveEulerProduct z ^ 2 ≤
        2 * C * Real.exp (2 * C) * Real.exp (-(2 * (m : ℝ))) := by
  let B := cubicSieveBlockIndices z
  let C := Real.exp (12 * A)
  let u (j : ℕ) := cubicSieveDivisorBlockUpperRatio z m j 1
  let e (j : ℕ) := cubicSieveDivisorBlockOverflowRatio z m j 1
  have hdata (j : ℕ) := cubicSieve_divisorBlock_relative_data hz hA m j (hmass j)
  have hU₀ (j : ℕ) : 0 ≤ u j := (hdata j).1
  have hU (j : ℕ) : u j ≤ 1 + C * cubicSieveBlockLoss m j := (hdata j).2.1
  have hE₀ (j : ℕ) : 0 ≤ e j := (hdata j).2.2.1
  have hE (j : ℕ) : e j ≤ C * cubicSieveBlockLoss m j := (hdata j).2.2.2.1
  dsimp only
  rw [cubicSieve_divisorModel_normalized_eq_blocks]
  change 0 ≤ (∑ j ∈ B, e j * ∏ i ∈ B.erase j, u i) ∧
    (∑ j ∈ B, e j * ∏ i ∈ B.erase j, u i) ≤
      2 * C * Real.exp (2 * C) * Real.exp (-(2 * (m : ℝ)))
  refine ⟨sum_nonneg (fun j _ => mul_nonneg (hE₀ j) (prod_nonneg (fun i _ => hU₀ i))), ?_⟩
  calc
    _ ≤ ∑ j ∈ B, (C * Real.exp (2 * C)) * cubicSieveBlockLoss m j := by
      apply sum_le_sum
      intro j _
      have hP := cubicSieve_blockProducts_le (B.erase j) u hm (Real.exp_pos _).le
        (fun i _ => hU₀ i) (fun i _ => hU i)
      exact (mul_le_mul (hE j) hP (prod_nonneg (fun i _ => hU₀ i))
        (by unfold C cubicSieveBlockLoss; positivity)
        ).trans_eq (by ring)
    _ = (C * Real.exp (2 * C)) * ∑ j ∈ B, cubicSieveBlockLoss m j := (mul_sum _ _ _).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left (cubicSieve_blockLoss_sum_le B hm) (by positivity)).trans_eq
      (by ring)

theorem cubicSieve_divisorModel_normalized_derivative_bound {z A : ℝ} (hz : 1 < z) (hA : 0 ≤ A)
    {m : ℕ} (hm : 1 ≤ m)
    (hmass : ∀ j, (∑ p ∈ cubicSieveBlock z j, cubicSievePrimeDivisorDensity p) ≤ A) :
    let C := Real.exp (12 * A)
    |cubicSieveDivisorModelNormalizedDerivative z m| ≤
      2 * C * Real.exp (2 * C) * (1 + 4 * C) * Real.log z * Real.exp (-(2 * (m : ℝ))) := by
  let B := cubicSieveBlockIndices z
  let C := Real.exp (12 * A)
  let L := Real.log z
  let P := Real.exp (2 * C)
  let u (j : ℕ) := cubicSieveDivisorBlockUpperRatio z m j 1
  let e (j : ℕ) := cubicSieveDivisorBlockOverflowRatio z m j 1
  let u' := cubicSieveDivisorBlockUpperTangent z m
  let e' := cubicSieveDivisorBlockOverflowTangent z m
  have hL : 0 ≤ L := (Real.log_pos hz).le
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hdata (j : ℕ) := cubicSieve_divisorBlock_relative_data hz hA m j (hmass j)
  have hU₀ (j : ℕ) : 0 ≤ u j := (hdata j).1
  have hU (j : ℕ) : u j ≤ 1 + C * cubicSieveBlockLoss m j := (hdata j).2.1
  have hE₀ (j : ℕ) : 0 ≤ e j := (hdata j).2.2.1
  have hE (j : ℕ) : e j ≤ C * cubicSieveBlockLoss m j := (hdata j).2.2.2.1
  have hUd (j : ℕ) : |u' j| ≤ 2 * C * L * (1 / 2 : ℝ) ^ j := (hdata j).2.2.2.2.1
  have hEd (j : ℕ) : |e' j| ≤ L * C * cubicSieveBlockLoss m j :=
    (hdata j).2.2.2.2.2.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right hL (pow_le_one₀ (by norm_num) (by norm_num))) hC)
        (by unfold cubicSieveBlockLoss; positivity))
  dsimp only
  change |∑ j ∈ B, (e' j * (∏ i ∈ B.erase j, u i) +
    e j * cubicSieveProdTangent (B.erase j) u u')| ≤
      2 * C * P * (1 + 4 * C) * L * Real.exp (-(2 * (m : ℝ)))
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ j ∈ B, (C * P * (1 + 4 * C) * L) * cubicSieveBlockLoss m j := by
      apply sum_le_sum
      intro j _
      have hprod : (∏ i ∈ B.erase j, u i) ≤ P :=
        cubicSieve_blockProducts_le _ u hm hC (fun i _ => hU₀ i) (fun i _ => hU i)
      have hprod₀ : 0 ≤ ∏ i ∈ B.erase j, u i := prod_nonneg (fun i _ => hU₀ i)
      have ht : |cubicSieveProdTangent (B.erase j) u u'| ≤ 4 * C * P * L :=
        cubicSieve_blockProducts_tangent_le _ u u' hm hC hL
          (fun i _ => hU₀ i) (fun i _ => hU i) (fun i _ => hUd i)
      refine (abs_add_le _ _).trans ?_
      simp only [abs_mul, abs_of_nonneg hprod₀, abs_of_nonneg (hE₀ j)]
      exact (add_le_add (mul_le_mul (hEd j) hprod hprod₀
        (mul_nonneg (mul_nonneg hL hC) (by unfold cubicSieveBlockLoss; positivity)))
        (mul_le_mul (hE j) ht (abs_nonneg _) (by unfold cubicSieveBlockLoss; positivity))).trans_eq
        (by ring)
    _ = (C * P * (1 + 4 * C) * L) * ∑ j ∈ B, cubicSieveBlockLoss m j := (mul_sum _ _ _).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left (cubicSieve_blockLoss_sum_le B hm) (by positivity)).trans_eq
      (by ring)

theorem cubicSieve_divisorModel_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 1 < z → ∀ m : ℕ, 1 ≤ m →
      0 ≤ cubicSieveDivisorCorrectionModel z m 1 ∧
      cubicSieveDivisorCorrectionModel z m 1 ≤
        C * Real.exp (-(2 * (m : ℝ))) * markedSieveEulerProduct z ^ 2 ∧
      |deriv (cubicSieveDivisorCorrectionModel z m) 1| ≤
        C * Real.log z * Real.exp (-(2 * (m : ℝ))) * markedSieveEulerProduct z ^ 2 := by
  obtain ⟨A, hA, hmass⟩ := cubicSieve_block_divisorDensity_mass_bound
  let K := Real.exp (12 * A)
  let C := 2 * K * Real.exp (2 * K) * (1 + 4 * K)
  refine ⟨C, by positivity, ?_⟩
  intro z hz m hm
  have hEuler : 0 < markedSieveEulerProduct z ^ 2 := pow_pos (markedSieveEulerProduct_pos z) _
  obtain ⟨hV₀, hV⟩ := cubicSieve_divisorModel_normalized_value_bound hz hA hm (hmass z hz)
  have hD := cubicSieve_divisorModel_normalized_derivative_bound hz hA hm (hmass z hz)
  have hV₀' := mul_nonneg hV₀ hEuler.le
  rw [div_mul_cancel₀ _ hEuler.ne'] at hV₀'
  refine ⟨hV₀', ?_, ?_⟩
  · apply (div_le_iff₀ hEuler).mp
    exact hV.trans (mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (by positivity : 0 ≤ 2 * K * Real.exp (2 * K))
        (le_add_of_nonneg_right (by positivity : 0 ≤ 4 * K))) (Real.exp_pos _).le)
  · rw [cubicSieve_divisorModel_deriv_one, abs_mul, abs_of_pos hEuler]
    exact mul_le_mul_of_nonneg_right hD hEuler.le

theorem cubicSieve_divisorModel_log_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z : ℝ in atTop, ∀ m : ℕ, 1 ≤ m →
      0 ≤ cubicSieveDivisorCorrectionModel z m 1 ∧
      cubicSieveDivisorCorrectionModel z m 1 ≤ C * Real.exp (-(2 * (m : ℝ))) / (Real.log z) ^ 2 ∧
      |deriv (cubicSieveDivisorCorrectionModel z m) 1| ≤
        C * Real.exp (-(2 * (m : ℝ))) / Real.log z := by
  obtain ⟨C, hC, hmodel⟩ := cubicSieve_divisorModel_bounds
  let K := Real.exp (1 - Real.eulerMascheroniConstant)
  refine ⟨C * K ^ 2, by positivity, ?_⟩
  filter_upwards [markedSieveEulerProduct_upper_eventually, eventually_gt_atTop (1 : ℝ)]
    with z hzM hz
  intro m hm
  obtain ⟨h0, hV, hD⟩ := hmodel z hz m hm
  have hL := Real.log_pos hz
  have hP : markedSieveEulerProduct z ^ 2 ≤ (K / Real.log z) ^ 2 :=
    pow_le_pow_left₀ (markedSieveEulerProduct_pos z).le hzM 2
  refine ⟨h0, ?_, ?_⟩
  · exact hV.trans ((mul_le_mul_of_nonneg_left hP (by positivity)).trans_eq (by ring))
  · exact hD.trans ((mul_le_mul_of_nonneg_left hP (by positivity)).trans_eq (by
      field_simp [hL.ne']))

end ArtinMatthews
