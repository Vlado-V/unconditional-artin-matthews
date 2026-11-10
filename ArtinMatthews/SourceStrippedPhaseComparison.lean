module

public import ArtinMatthews.SourceLocalPhaseComparison
public import ArtinMatthews.ProbeIdealLocalCoefficient
public import ArtinMatthews.SourceGammaFiniteFProduct
public import ArtinMatthews.ProbeIdealGaussValues
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact residue-phase covariance of the stripped coefficient at all
modulus and frequency orders. In the zero-frequency interior cases the
positive-modulus mask forces the relevant character power to be trivial. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open SIntegerFourier SIntegerPrincipalization StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable (P : SourceExteriorPrime F S₀)

local notation "κ" => ((𝓞 F) ⧸ P.val.asIdeal)
local notation "χ" => reflectionPrimeCharacters F hζ S₀ P
local notation "seed" => sourceHilbertSeed F S₀
private theorem sourcePrimeStripExterior : P.val ∉ principalizingSet seed := P.property

private def sourcePrimeStripGenerator : PrincipalIntegerRing seed :=
  sourceAllowedPrimeGenerator F hζ S₀ P

private theorem sourcePrimeStripGenerator_ideal :
    P.val.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing seed)) =
      Ideal.span {sourcePrimeStripGenerator F hζ S₀ P} :=
  sourceAllowedPrimeGenerator_ideal F hζ S₀ P

local notation "hP" => sourcePrimeStripExterior F S₀ P
local notation "p" => sourcePrimeStripGenerator F hζ S₀ P
local notation "hp" => sourcePrimeStripGenerator_ideal F hζ S₀ P
local notation "C" => sourcePrimeStrippedCoefficient F hζ S₀ P
local notation "C₀" => probeIdealLocalCoefficient F P.val χ
local notation "τ" => residueSourceTau seed P.val hP p hp
local notation "τ₀" => probeIdealTau F P.val
local instance sourceStripField : Field κ := Ideal.Quotient.field _

theorem sourcePrimePhase_inv_pow_dvd (a : κˣ) (v : ℕ) (hv : 6 ∣ v) :
    (χ a)⁻¹ ^ v = 1 := by
  obtain ⟨d, rfl⟩ := hv
  rw [pow_mul, inv_pow, sourcePrimeCharacter_unit_pow_six F hζ S₀ P a, inv_one, one_pow]

include hS

theorem sourcePrimeStrippedCoefficient_mulShift_zero (a : κˣ)
    (ha : sourcePrimeResiduePhase F hζ S₀ P = (probeIdealResiduePhase F P.val).mulShift a)
    (n J : ℕ) : C (n + 1) 0 J = (χ a)⁻¹ ^ (n + 1) * C₀ (n + 1) 0 J := by
  have hχ := sourcePrimeCharacter_order F hζ S₀ P
  have hbad := sourceExteriorPrime_not_traceBad F S₀ hS P
  have hτ : τ (χ ^ (n + 1)) = (χ a)⁻¹ ^ (n + 1) * τ₀ (χ ^ (n + 1)) :=
    sourcePrimeTau_mulShift F hζ S₀ P a ha (n + 1)
  change standardLocalCoefficient seed P.val hP p hp χ (n + 1) 0 J = _
  rw [standardLocalCoefficient_succ_zero seed P.val hP p hp
    hbad χ hχ n J, show C₀ (n + 1) 0 J = probeIdealLocalCZero F P.val χ n J from rfl,
    probeIdealLocalCZero_eq, probeIdealResidueTransform_prime_pow F P.val χ hχ]
  by_cases hn : n ≤ J
  · rw [ite_eq_left hn, ite_eq_left hn]
    by_cases h : n = J
    · rw [ite_eq_left h, ite_eq_left (show J - n = 0 by omega), hτ]
      ring
    · rw [ite_eq_right h, ite_eq_right (show J - n ≠ 0 by omega)]
      by_cases hd : 6 ∣ n + 1
      · rw [ite_eq_left hd, sourcePrimePhase_inv_pow_dvd F hζ S₀ P a _ hd, one_mul]
      · simp only [ite_eq_right hd, mul_zero]
  · simp only [ite_eq_right hn, mul_zero]

theorem sourcePrimeStrippedCoefficient_mulShift_one (a : κˣ)
    (ha : sourcePrimeResiduePhase F hζ S₀ P = (probeIdealResiduePhase F P.val).mulShift a)
    (n J : ℕ) : C (n + 1) 1 J = (χ a)⁻¹ ^ (n + 1) * C₀ (n + 1) 1 J := by
  have hχ := sourcePrimeCharacter_order F hζ S₀ P
  have hminus := sourcePrimeCharacter_minus_one F hζ S₀ P
  have hbad := sourceExteriorPrime_not_traceBad F S₀ hS P
  have hτ : τ (χ ^ n) = (χ a)⁻¹ ^ n * τ₀ (χ ^ n) :=
    sourcePrimeTau_mulShift F hζ S₀ P a ha n
  have hτ₁ : τ χ = (χ a)⁻¹ * τ₀ χ := by
    have h := sourcePrimeTau_mulShift F hζ S₀ P a ha 1
    simp only [pow_one] at h
    exact h
  change standardLocalCoefficient seed P.val hP p hp χ (n + 1) 1 J = _
  rw [standardLocalCoefficient_succ_one seed P.val hP p hp
    hbad χ hχ hminus n J, show C₀ (n + 1) 1 J = probeIdealLocalCOne F P.val χ n J from rfl,
    probeIdealLocalCOne_eq F P.val χ hminus, probeIdealResidueTransform_prime_pow F P.val χ hχ]
  by_cases hn : n + 1 ≤ J
  · rw [ite_eq_left hn, ite_eq_left hn, hτ₁]
    by_cases h : n + 1 = J
    · rw [ite_eq_left h, ite_eq_left (show J - (n + 1) = 0 by omega), hτ, pow_succ (χ a)⁻¹ n]
      ring
    · rw [ite_eq_right h, ite_eq_right (show J - (n + 1) ≠ 0 by omega)]
      by_cases hd : 6 ∣ n
      · rw [ite_eq_left hd, pow_succ (χ a)⁻¹ n,
          sourcePrimePhase_inv_pow_dvd F hζ S₀ P a n hd, one_mul]
        ring
      · simp only [ite_eq_right hd, mul_zero]
  · simp only [ite_eq_right hn, mul_zero]

theorem sourcePrimeStrippedCoefficient_mulShift (a : κˣ)
    (ha : sourcePrimeResiduePhase F hζ S₀ P = (probeIdealResiduePhase F P.val).mulShift a)
    (t k J : ℕ) : C t k J = (χ a)⁻¹ ^ t * C₀ t k J := by
  cases t with
  | zero =>
      cases k with
      | zero =>
          rw [sourcePrimeStrippedCoefficient_zero_zero, probeIdealLocalCoefficient_zero_zero,
            pow_zero, one_mul]
      | succ k =>
          change standardLocalCoefficient seed P.val hP p hp χ 0 (k + 1) J = _
          rw [standardLocalCoefficient_zero_succ seed P.val hP p hp χ k J,
            show C₀ 0 (k + 1) J = probeIdealLocalInnerAbsent F P.val χ k J from rfl,
            probeIdealLocalInnerAbsent_eq, pow_zero, one_mul]
  | succ n =>
      cases k with
      | zero => exact sourcePrimeStrippedCoefficient_mulShift_zero F hζ S₀ hS P a ha n J
      | succ k =>
          cases k with
          | zero => exact sourcePrimeStrippedCoefficient_mulShift_one F hζ S₀ hS P a ha n J
          | succ k =>
              change standardLocalCoefficient seed P.val hP p hp χ (n + 1) (k + 2) J = _
              rw [standardLocalCoefficient_succ_add_two seed P.val
                hP p hp (sourceExteriorPrime_not_traceBad F S₀ hS P),
                probeIdealLocalCoefficient_higher, mul_zero]

end
end ArtinMatthews.SourceEulerAssembly
