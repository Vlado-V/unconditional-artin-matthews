module

public import ArtinMatthews.CubicThetaSeries
public import ArtinMatthews.CubicThetaCoefficients
public import ArtinMatthews.CubicThetaIdealSum
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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

/-!
# The actual holomorphic Eisenstein Hecke theta series

Starting with a unit-invariant residue character of the Eisenstein integers,
we sum its ideal character over ideals of each norm and construct the resulting
holomorphic q-series. Its coefficients are proved to be those exact finite
ideal sums; its constant term is zero and its first coefficient is one.

This is not yet a construction of a `CuspForm`: the modular transformation law
and vanishing at every other cusp remain to be established.
-/

noncomputable section
open scoped Topology Manifold
open Complex UpperHalfPlane Filter
open OAI.SevenEighths

namespace ArtinMatthews

/-- The theta series with coefficients given by the genuine finite ideal sums. -/
def heckeTheta (χ : HeckeFamily.Character) : ℍ → ℂ :=
  thetaFromCoefficients (idealThetaCoeff χ)

private theorem idealThetaCoeff_polynomial_bound (χ : HeckeFamily.Character) :
    ∀ n, ‖idealThetaCoeff χ n‖ ≤ (64 : ℝ) * ((n : ℝ) ^ 1 + 1) := by
  simpa only [pow_one] using idealThetaCoeff_norm_le χ

/-- The defining series converges on the entire upper half plane. -/
theorem heckeTheta_hasSum (χ : HeckeFamily.Character) (τ : ℍ) :
    HasSum (fun n : ℕ => idealThetaCoeff χ n * Function.Periodic.qParam 1 τ ^ n)
      (heckeTheta χ τ) :=
  thetaFromCoefficients_hasSum (by norm_num) (idealThetaCoeff_polynomial_bound χ) τ

/-- The constructed function is the convergent sum over actual integral ideals,
with precisely the character and absolute-norm exponents of Hecke theta. -/
theorem heckeTheta_hasSum_ideals (χ : HeckeFamily.Character) (τ : ℍ) :
    HasSum (fun I : Ideal HeckeFamily.O =>
      thetaIdealCharacter χ I * Function.Periodic.qParam 1 τ ^ I.absNorm)
      (heckeTheta χ τ) := by
  have hq := Function.Periodic.norm_qParam_lt_one (by norm_num : (0 : ℝ) < 1) τ.im_pos
  have hs := (idealTheta_summable_norm χ hq).of_norm.hasSum
  rw [idealTheta_tsum_eq_coefficients χ hq] at hs
  exact hs

/-- The actual ideal theta series is holomorphic. -/
theorem heckeTheta_mdiff (χ : HeckeFamily.Character) : MDiff (heckeTheta χ) :=
  thetaFromCoefficients_mdiff (by norm_num) (idealThetaCoeff_polynomial_bound χ)

/-- The actual ideal theta series has period one. -/
theorem heckeTheta_periodic (χ : HeckeFamily.Character) :
    Function.Periodic (heckeTheta χ ∘ ofComplex) (1 : ℂ) :=
  thetaFromCoefficients_periodic (idealThetaCoeff χ)

/-- It vanishes at the infinite cusp. This does not assert vanishing at the
other cusps of a congruence subgroup. -/
theorem heckeTheta_zeroAtInfty (χ : HeckeFamily.Character) :
    IsZeroAtImInfty (heckeTheta χ) :=
  thetaFromCoefficients_zeroAtInfty (by norm_num)
    (idealThetaCoeff_polynomial_bound χ) (idealThetaCoeff_zero χ)

/-- Exact identification with the finite ideal-sum coefficients. -/
theorem heckeTheta_qExpansion_coeff (χ : HeckeFamily.Character) (n : ℕ) :
    (qExpansion 1 (heckeTheta χ)).coeff n = idealThetaCoeff χ n :=
  (thetaFromCoefficients_qExpansion_coeff (by norm_num)
    (idealThetaCoeff_polynomial_bound χ) (idealThetaCoeff_zero χ) n).symm

@[simp] theorem heckeTheta_constantTerm (χ : HeckeFamily.Character) :
    (qExpansion 1 (heckeTheta χ)).coeff 0 = 0 := by
  rw [heckeTheta_qExpansion_coeff, idealThetaCoeff_zero]

@[simp] theorem heckeTheta_firstCoeff (χ : HeckeFamily.Character) :
    (qExpansion 1 (heckeTheta χ)).coeff 1 = 1 := by
  rw [heckeTheta_qExpansion_coeff, idealThetaCoeff_one]

/-- The construction is nonzero: its first Fourier coefficient is one. -/
theorem heckeTheta_ne_zero (χ : HeckeFamily.Character) : heckeTheta χ ≠ 0 := by
  intro hzero
  have h := heckeTheta_firstCoeff χ
  rw [hzero, qExpansion_zero] at h
  simp at h

end ArtinMatthews
