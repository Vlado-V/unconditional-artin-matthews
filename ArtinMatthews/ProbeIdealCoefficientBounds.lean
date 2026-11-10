module

public import ArtinMatthews.ProbeIdealLocalCoefficient
public import ArtinMatthews.ProbeIdealGaussValues
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Norm and support bounds for the genuine local finite sums at a prime
dividing the sixth-free parameter. No estimate for C is an input. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem probeIdealNorm_one_le (P : HeightOneSpectrum (𝓞 K)) :
    1 ≤ (Ideal.absNorm (P.asIdeal) : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)

theorem probeIdealTau_norm_le_sqrt (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) :
    ‖probeIdealTau K P χ‖ ≤ Real.sqrt (Ideal.absNorm (P.asIdeal) : ℝ) := by
  by_cases hχ : χ = 1
  · rw [hχ, probeIdealTau_principal K P, norm_neg, norm_one]
    have hQ := probeIdealNorm_one_le K P
    nlinarith [Real.sqrt_nonneg (Ideal.absNorm (P.asIdeal) : ℝ),
      Real.sq_sqrt (by positivity : 0 ≤ (Ideal.absNorm (P.asIdeal) : ℝ))]
  · exact (probeIdealTau_norm K P χ hχ).le

theorem probeIdealResidueTransform_prime_pow_norm_le (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6) (v J : ℕ) :
    ‖probeIdealResidueTransform K P χ v (probeIdealUniformizer P ^ J)‖ ≤
      (Ideal.absNorm (P.asIdeal) : ℝ) := by
  have hQ := probeIdealNorm_one_le K P
  rw [probeIdealResidueTransform_prime_pow K P χ hχ]
  split_ifs
  · apply (probeIdealTau_norm_le_sqrt K P (χ ^ v)).trans
    nlinarith [Real.sqrt_nonneg (Ideal.absNorm (P.asIdeal) : ℝ),
      Real.sq_sqrt (by positivity : 0 ≤ (Ideal.absNorm (P.asIdeal) : ℝ))]
  · have hreal : (Ideal.absNorm (P.asIdeal) : ℂ) - 1 =
        (((Ideal.absNorm (P.asIdeal) : ℝ) - 1 : ℝ) : ℂ) := by
      simp only [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one]
    rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  · simp only [norm_zero]
    positivity

theorem probeIdealLocalCZero_norm_le (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6) (n J : ℕ) :
    ‖probeIdealLocalCZero K P χ n J‖ ≤
      (Ideal.absNorm (P.asIdeal) : ℝ) ^ (n + 1) := by
  rw [probeIdealLocalCZero_eq K P χ]
  split_ifs
  · rw [norm_mul, norm_pow, Complex.norm_natCast, pow_succ]
    exact mul_le_mul_of_nonneg_left
      (probeIdealResidueTransform_prime_pow_norm_le K P χ hχ _ _) (by positivity)
  · simp

theorem probeIdealLocalCOne_norm_le (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (n J : ℕ) :
    ‖probeIdealLocalCOne K P χ n J‖ ≤
      Real.sqrt (Ideal.absNorm (P.asIdeal) : ℝ) *
        (Ideal.absNorm (P.asIdeal) : ℝ) ^ (n + 1) := by
  rw [probeIdealLocalCOne_eq K P χ hminus]
  split_ifs
  · rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, pow_succ, ← mul_assoc]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (probeIdealTau_norm_le_sqrt K P χ) (by positivity))
      (probeIdealResidueTransform_prime_pow_norm_le K P χ hχ _ _)
      (norm_nonneg _) (by positivity)
  · simp only [norm_zero]
    positivity

theorem probeIdealLocalCoefficient_zero_norm_le (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6) (t J : ℕ) :
    ‖probeIdealLocalCoefficient K P χ t 0 J‖ ≤
      (Ideal.absNorm (P.asIdeal) : ℝ) ^ t := by
  cases t with
  | zero => simp [probeIdealLocalCoefficient_zero_zero]
  | succ n => exact probeIdealLocalCZero_norm_le K P χ hχ n J

theorem probeIdealLocalCoefficient_one_norm_le (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (t J : ℕ) :
    ‖probeIdealLocalCoefficient K P χ t 1 J‖ ≤
      Real.sqrt (Ideal.absNorm (P.asIdeal) : ℝ) *
        (Ideal.absNorm (P.asIdeal) : ℝ) ^ t := by
  cases t with
  | zero =>
    change ‖probeIdealLocalInnerAbsent K P χ 0 J‖ ≤ _
    rw [probeIdealLocalInnerAbsent_eq K P χ, pow_zero, mul_one]
    split_ifs
    · have hQ := probeIdealNorm_one_le K P
      simp only [norm_one]
      nlinarith [Real.sqrt_nonneg (Ideal.absNorm (P.asIdeal) : ℝ),
        Real.sq_sqrt (by positivity : 0 ≤ (Ideal.absNorm (P.asIdeal) : ℝ))]
    · simp
  | succ n => exact probeIdealLocalCOne_norm_le K P χ hχ hminus n J

theorem probeIdealLocalCoefficient_zero_bad_outer (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k J : ℕ) (hJ : 0 < J) :
    probeIdealLocalCoefficient K P χ 0 (k + 1) J = 0 := by
  change probeIdealLocalInnerAbsent K P χ k J = 0
  rw [probeIdealLocalInnerAbsent_eq K P χ, ite_eq_right (by omega)]

theorem probeIdealLocalCoefficient_bad_higher (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (t k J : ℕ) (hJ : 0 < J) :
    probeIdealLocalCoefficient K P χ t (k + 2) J = 0 := by
  cases t with
  | zero => exact probeIdealLocalCoefficient_zero_bad_outer K P χ (k + 1) J hJ
  | succ n => exact probeIdealLocalCoefficient_higher K P χ n k J

theorem probeIdealLocalCoefficient_bad_first_zero (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (J : ℕ) (hJ : 0 < J) :
    probeIdealLocalCoefficient K P χ 1 0 J = 0 := by
  change probeIdealLocalCZero K P χ 0 J = 0
  rw [probeIdealLocalCZero_eq K P χ, ite_eq_left (Nat.zero_le _), pow_zero,
    Nat.sub_zero, one_mul, probeIdealResidueTransform_prime_pow K P χ hχ,
    ite_eq_right (by omega), ite_eq_right (by omega)]

end
end ArtinMatthews.VaryingKummerAnalytic
