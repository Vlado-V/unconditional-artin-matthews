module

public import ArtinMatthews.ProbeIdealLocalScalars
public import ArtinMatthews.ProbeIdealGaussPhase
public import ArtinMatthews.ProbeIdealGaussValues
public import ArtinMatthews.ProbePrimeSixthTable
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The nonzero j=0 local coefficients, with J=6*r.  The index n still
means t=n+1.  These are evaluations of the literal frozen local sums. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probeIdealLocalCZero_off_classes (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (n r : ℕ) (hn : ¬ 6 ∣ n) (hn1 : ¬ 6 ∣ n + 1) :
    probeIdealLocalCZero K P χ n (6 * r) = 0 := by
  rw [probeIdealLocalCZero_eq K P χ]
  split_ifs with hnr
  · rw [probeIdealResidueTransform_prime_pow K P χ hχ]
    have hdiff : 6 * r - n ≠ 0 := by omega
    rw [ite_eq_right hdiff, ite_eq_right hn1, mul_zero]
  · rfl

theorem probeIdealLocalCOne_off_classes (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (n r : ℕ) (hn : ¬ 6 ∣ n) (hn1 : ¬ 6 ∣ n + 1) :
    probeIdealLocalCOne K P χ n (6 * r) = 0 := by
  rw [probeIdealLocalCOne_eq K P χ hminus]
  split_ifs with hnr
  · rw [probeIdealResidueTransform_prime_pow K P χ hχ]
    have hdiff : 6 * r - (n + 1) ≠ 0 := by omega
    rw [ite_eq_right hdiff, ite_eq_right hn, mul_zero]
  · rfl

theorem probeIdealLocalCZero_one_class (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6) (d r : ℕ) :
    probeIdealLocalCZero K P χ (6 * d) (6 * r) =
      if r = d then (Ideal.absNorm (P.asIdeal) : ℂ) ^ (6 * d) *
        probeIdealTau K P χ else 0 := by
  have h6 : χ ^ 6 = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [hχ])
  rw [probeIdealLocalCZero_eq K P χ]
  by_cases hdr : r = d
  · subst r
    rw [ite_eq_left le_rfl, Nat.sub_self,
      probeIdealResidueTransform_prime_pow K P χ hχ, ite_eq_left rfl,
      ite_eq_left rfl, probeSextic_power_reduce χ h6 d 1, pow_one]
  · rw [ite_eq_right hdr]
    split_ifs with hle
    · rw [probeIdealResidueTransform_prime_pow K P χ hχ,
        ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
    · rfl

theorem probeIdealLocalCOne_one_class (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (d r : ℕ) :
    probeIdealLocalCOne K P χ (6 * d) (6 * r) =
      if d < r then probeIdealTau K P χ *
        (Ideal.absNorm (P.asIdeal) : ℂ) ^ (6 * d) *
          ((Ideal.absNorm (P.asIdeal) : ℂ) - 1) else 0 := by
  rw [probeIdealLocalCOne_eq K P χ hminus]
  by_cases hdr : d < r
  · rw [ite_eq_left (by omega), ite_eq_left hdr,
      probeIdealResidueTransform_prime_pow K P χ hχ,
      ite_eq_right (by omega), ite_eq_left (dvd_mul_right 6 d)]
  · rw [ite_eq_right (by omega), ite_eq_right hdr]

theorem probeIdealLocalCZero_zero_class (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6) (d r : ℕ) :
    probeIdealLocalCZero K P χ (6 * d + 5) (6 * r) =
      if d < r then (Ideal.absNorm (P.asIdeal) : ℂ) ^ (6 * d + 5) *
        ((Ideal.absNorm (P.asIdeal) : ℂ) - 1) else 0 := by
  rw [probeIdealLocalCZero_eq K P χ]
  by_cases hdr : d < r
  · rw [ite_eq_left (by omega), ite_eq_left hdr,
      probeIdealResidueTransform_prime_pow K P χ hχ,
      ite_eq_right (by omega), ite_eq_left (by omega)]
  · rw [ite_eq_right (by omega), ite_eq_right hdr]

theorem probeIdealLocalCOne_zero_class (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (d r : ℕ) :
    probeIdealLocalCOne K P χ (6 * d + 5) (6 * r) =
      if r = d + 1 then (Ideal.absNorm (P.asIdeal) : ℂ) ^ (6 * d + 6) else 0 := by
  have h6 : χ ^ 6 = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [hχ])
  rw [probeIdealLocalCOne_eq K P χ hminus]
  by_cases hdr : r = d + 1
  · subst r
    rw [ite_eq_left (by omega), ite_eq_left rfl,
      probeIdealResidueTransform_prime_pow K P χ hχ,
      ite_eq_left (by omega), probeSextic_power_reduce χ h6 d 5]
    calc
      _ = (Ideal.absNorm (P.asIdeal) : ℂ) ^ (6 * d + 5) *
          (probeIdealTau K P χ * probeIdealTau K P (χ ^ 5)) := by ring
      _ = _ := by rw [probeIdealGauss_inverse_pair K P χ hχ hminus, ← pow_succ]
  · rw [ite_eq_right hdr]
    split_ifs with hle
    · rw [probeIdealResidueTransform_prime_pow K P χ hχ,
        ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
    · rfl

end

end ArtinMatthews.VaryingKummerAnalytic
