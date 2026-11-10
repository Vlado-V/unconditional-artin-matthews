module

public import ArtinMatthews.SourceQuadraticDualFiniteErrors
public import ArtinMatthews.SourceQuadraticSmallResidue
public import ArtinMatthews.QuadraticHeckeCutoffWeightBounds
public import ArtinMatthews.SourceQuadraticEuler
public import ArtinMatthews.SourceQuadraticFullResidue
public import ArtinMatthews.SourceQuadraticPrincipalNormPoisson
public import ArtinMatthews.SourceQuadraticResidueScalarPositive
public import ArtinMatthews.VaryingKummerAnalyticHeckeFiniteEulerAlgebra
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The zero-exponent Full residue is a product of nonnegative real
factors, including the full divisor factor for the fixed and common modulus. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "E" => SourcePrimeExponents F S₀
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ

theorem sourceQuadraticPrincipalHalfCoefficient_ofReal (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥) :
    quadraticHeckeHalfCoefficient F (Ψ 0) J =
      ((Real.sqrt (Ideal.absNorm J : ℝ))⁻¹ : ℝ) := by
  rw [quadraticHeckeHalfCoefficient_eq_div_sqrt,
    sourceQuadraticRayCharacter_zero_allCoefficient F S₀ hζ J hJ, one_div, Complex.ofReal_inv]

theorem sourceQuadraticPrincipalEuler_ofReal (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    (∑ d ∈ HeckeIdealMobius.divisors F m,
      (moebius d : ℂ) * quadraticHeckeHalfCoefficient F (Ψ 0) d) =
        ((∏ P ∈ HeckeIdealMobius.primeSupport F m,
          (1 - (Real.sqrt (Ideal.absNorm P : ℝ))⁻¹) : ℝ) : ℂ) := by
  rw [← HeckeIdealMobius.prime_product_eq_moebius_sum F m hm, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro P hP
  rw [sourceQuadraticPrincipalHalfCoefficient_ofReal F S₀ hζ P
    (HeckeIdealMobius.support_prime F hP).ne_zero]
  simp only [Complex.ofReal_sub, Complex.ofReal_one]

theorem sourceQuadraticPrincipalEuler_nonnegative (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    0 ≤ (∑ d ∈ HeckeIdealMobius.divisors F m,
      (moebius d : ℂ) * quadraticHeckeHalfCoefficient F (Ψ 0) d).re ∧
      (∑ d ∈ HeckeIdealMobius.divisors F m,
        (moebius d : ℂ) * quadraticHeckeHalfCoefficient F (Ψ 0) d).im = 0 := by
  rw [sourceQuadraticPrincipalEuler_ofReal F S₀ hζ m hm]
  simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  apply Finset.prod_nonneg
  intro P hP
  apply sub_nonneg.mpr
  apply inv_le_one_of_one_le₀
  apply Real.one_le_sqrt.mpr
  exact_mod_cast Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr (HeckeIdealMobius.support_prime F hP).ne_zero)

theorem sourceQuadraticPrincipalCutoff_ofReal (K : ℝ) :
    (∑ a ∈ quadraticHeckeSquarefreeCutoff F K, quadraticHeckeHalfCoefficient F (Ψ 0) a) =
      ((∑ a ∈ quadraticHeckeSquarefreeCutoff F K,
        (Real.sqrt (Ideal.absNorm a : ℝ))⁻¹ : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact sourceQuadraticPrincipalHalfCoefficient_ofReal F S₀ hζ a
    ((mem_quadraticHeckeSquarefreeCutoff F).mp ha).1.ne_zero

theorem sourceQuadraticPrincipalCutoff_nonnegative (K : ℝ) :
    0 ≤ (∑ a ∈ quadraticHeckeSquarefreeCutoff F K, quadraticHeckeHalfCoefficient F (Ψ 0) a).re ∧
      (∑ a ∈ quadraticHeckeSquarefreeCutoff F K, quadraticHeckeHalfCoefficient F (Ψ 0) a).im = 0 := by
  rw [sourceQuadraticPrincipalCutoff_ofReal F S₀ hζ K]
  simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  exact Finset.sum_nonneg (fun a _ => inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem sourceQuadraticDualDivisorResidue_zero_nonnegative {M : ℝ} (hM : 0 < M)
    (K : ℝ) (g : E) :
    0 ≤ (sourceQuadraticDualDivisorResidue F S₀ hζ M K g 0).re ∧
      (sourceQuadraticDualDivisorResidue F S₀ hζ M K g 0).im = 0 := by
  have hρ : quadraticHeckeCoprimeDensity F (sourceQuadraticConductor F S₀ hζ 0) = 1 := by
    rw [sourceQuadraticConductor_zero]
    simp only [quadraticHeckeCoprimeDensity, HeckeIdealMobius.primeSupport,
      normalizedFactors_one, Multiset.toFinset_zero, Finset.prod_empty]
  rw [sourceQuadraticDualDivisorResidue_eq_halfCoefficient F S₀ hζ hM K g 0, hρ, mul_one]
  obtain ⟨hκ, hκi⟩ := sourceQuadraticSmallResidueFactor_nonnegative F M
  obtain ⟨hE, hEi⟩ := sourceQuadraticPrincipalEuler_nonnegative F S₀ hζ
    (sourceQuadraticBlockModulus F S₀ g) (sourceQuadraticBlockModulus_ne_bot F S₀ g)
  obtain ⟨hS, hSi⟩ := sourceQuadraticPrincipalCutoff_nonnegative F S₀ hζ K
  constructor
  · simp only [Complex.mul_re, Complex.mul_im, hκi, hEi, hSi, zero_mul, mul_zero,
      add_zero, sub_zero]
    exact mul_nonneg (mul_nonneg hκ hE) hS
  · simp only [Complex.mul_im, Complex.mul_re, hκi, hEi, hSi, zero_mul, mul_zero,
      add_zero, sub_zero]

end
end ArtinMatthews.SourceEulerAssembly
