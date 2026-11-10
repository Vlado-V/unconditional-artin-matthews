module

public import ArtinMatthews.CubicSieveRoughCarrier
public import ArtinMatthews.CubicSieveUpperSample
public import ArtinMatthews.QuadraticIdealNormCountGlobal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The replacement of the true rough gate by the upper polynomial is
charged to the exact divisor-weighted Section 7.1 overflow sum. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators Classical

def cubicSieveDivisorWeightedError {J : Type*} [Fintype J] (e : J → ℝ)
    (Φ : ℝ → ℝ) (γ x : ℝ) (m : ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊, Φ ((u : ℝ) / x) * literalMarkedArrayWeight e x u *
    ((u + 1).divisors.card : ℝ) * cubicSieveCorrection (x ^ γ) m (u + 1)

theorem cubicSieve_rough_sub_upper_norm_le {J : Type*} [Fintype J] (e : J → ℝ)
    (η : HeckeFamily.Character) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (Φ : ℝ → ℝ) (hΦ : ∀ t, 0 ≤ Φ t) (ε γ x : ℝ) (hx : 0 ≤ x) (m : ℕ)
    (hcore : ∀ u, ‖giantMarkedCenteredCore ε x u‖ ≤ 1) :
    ‖cubicSieveRoughThetaSum η χ (fun u => (literalMarkedArrayWeight e x u : ℂ)) Φ ε γ x -
      cubicSieveUpperThetaSum η χ (fun u => (literalMarkedArrayWeight e x u : ℂ)) Φ ε γ x m‖ ≤
      cubicSieveDivisorWeightedError e Φ γ x m := by
  let z := x ^ γ
  let U := Finset.Icc 1 ⌊2 * x⌋₊
  let B (u : ℕ) : ℂ := (literalMarkedArrayWeight e x u : ℂ) *
    giantMarkedCenteredCore ε x u * giantCubicSamplingKernel η χ Φ x 1 u
  let I (u : ℕ) : ℝ := if MarkedRoughAbove z (u + 1) then 1 else 0
  let F (u : ℕ) := cubicSieveUpper z m (u + 1)
  let E (u : ℕ) := cubicSieveCorrection z m (u + 1)
  have hR : cubicSieveRoughThetaSum η χ (fun u => (literalMarkedArrayWeight e x u : ℂ))
      Φ ε γ x = ∑ u ∈ U, B u * (I u : ℂ) := by
    unfold cubicSieveRoughThetaSum
    apply Finset.sum_congr rfl
    intro u _hu
    by_cases hr : MarkedRoughAbove (x ^ γ) (u + 1)
    · simp [I, z, hr, B]
    · simp [I, z, hr]
  rw [hR]
  change ‖(∑ u ∈ U, B u * (I u : ℂ)) - ∑ u ∈ U, B u * (F u : ℂ)‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ u ∈ U, ‖B u * ((I u : ℂ) - (F u : ℂ))‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro u _hu
      let W := literalMarkedArrayWeight e x u
      let φ := Φ ((u : ℝ) / x)
      let τ := ((u + 1).divisors.card : ℝ)
      have hW : 0 ≤ W := literalMarkedArrayWeight_nonneg e x u
      have hφ : 0 ≤ φ := hΦ _
      have hτ : 0 ≤ τ := Nat.cast_nonneg _
      have hg : 0 ≤ F u - I u ∧ F u - I u ≤ E u :=
        cubicSieve_upper_rough_error (Real.rpow_nonneg hx γ) m (u + 1)
      have hI : ‖(I u : ℂ) - (F u : ℂ)‖ ≤ E u := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
          abs_of_nonneg hg.1]
        exact hg.2
      have hK : ‖giantCubicSamplingKernel η χ Φ x 1 u‖ ≤ φ * τ := by
        simp only [giantCubicSamplingKernel, one_dvd, ite_true, norm_mul, Complex.norm_real]
        change ‖φ‖ * ‖idealThetaCoeff η (u + 1)‖ * ‖χ (u + 1)‖ ≤ _
        rw [Real.norm_of_nonneg hφ]
        exact (mul_le_of_le_one_right (mul_nonneg hφ (norm_nonneg _)) (χ.norm_le_one _)).trans
          (mul_le_mul_of_nonneg_left (idealThetaCoeff_norm_le_divisors_card η _) hφ)
      have hB : ‖B u‖ ≤ φ * W * τ := by
        dsimp only [B]
        simp only [norm_mul, Complex.norm_real]
        change ‖W‖ * ‖giantMarkedCenteredCore ε x u‖ *
          ‖giantCubicSamplingKernel η χ Φ x 1 u‖ ≤ _
        rw [Real.norm_of_nonneg hW]
        calc
          _ ≤ (W * 1) * (φ * τ) := mul_le_mul
            (mul_le_mul_of_nonneg_left (hcore u) hW) hK (norm_nonneg _) (mul_nonneg hW zero_le_one)
          _ = _ := by ring
      rw [norm_mul]
      exact mul_le_mul hB hI (norm_nonneg _) (mul_nonneg (mul_nonneg hφ hW) hτ)

end ArtinMatthews
