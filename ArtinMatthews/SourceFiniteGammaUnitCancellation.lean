module

public import ArtinMatthews.SourceActualCrossCancellation
public import ArtinMatthews.SourceFrequencyUnitReduction
public import ArtinMatthews.SourceCRTUnitRows
public import ArtinMatthews.SourceDirectedRowPowers
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

/-! The actual global gamma2 CRT factors cancel the directed finite-F
cofactor interactions, leaving the exact residual character of u. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "R" => sourceRing F S₀

theorem sourceFiniteGammaUnitFactor_cancel (c : ReflectionSquarefreeExponents F S₀)
    (l k r : SourcePrimeExponents F S₀) (u : R) (hu : u ≠ 0)
    (T : Finset (SourceExteriorPrime F S₀)) :
    let A := c.val + 3 • l
    (∏ P ∈ T, ∏ Q ∈ T, reflectionGaussPairKernel F hζ S₀ c P Q) *
      (∏ P : T, sourceExponentCRTUnitFactor F S₀ hζ (reflectionPrimeCharacters F hζ S₀) k A r u hu T P) =
        ∏ P : T, ((sourceResidualCharacterUnit F hζ S₀ u hu P.val ^
          ((k P.val : ℤ) - A P.val) : ℂˣ) : ℂ) := by
  let A := c.val + 3 • l
  let z := sourcePrimeCrossDiagonalUnit F hζ S₀
  let θ := sourceResidualCharacterUnit F hζ S₀ u hu
  let R₀ (P : SourceExteriorPrime F S₀) : ℂˣ := θ P ^ ((k P : ℤ) - A P) *
    ∏ Q ∈ T, z P Q ^ ((A P : ℤ) * k Q + ((A P : ℤ) - k P) * A Q)
  let W (P : SourceExteriorPrime F S₀) : ℂˣ := θ P ^ ((k P : ℤ) - A P)
  have hΓ : (∏ P ∈ T, ∏ Q ∈ T, reflectionGaussPairKernel F hζ S₀ c P Q) =
      ((∏ P ∈ T, ∏ Q ∈ T, z P Q ^ (2 * c.val P * c.val Q) : ℂˣ) : ℂ) := by
    simp only [reflectionGaussPairKernel_unit, Units.coe_prod, z]
  have hF : (∏ P : T, sourceExponentCRTUnitFactor F S₀ hζ (reflectionPrimeCharacters F hζ S₀) k A r u hu T P) =
      ((∏ P ∈ T, R₀ P : ℂˣ) : ℂ) := by
    calc
      _ = ∏ P : T, (R₀ P.val : ℂ) := by
        apply Finset.prod_congr rfl
        intro P _
        exact sourceExponentCRTUnitFactor_row F hζ S₀ T k A r u hu P
      _ = ∏ P ∈ T, (R₀ P : ℂ) := Finset.prod_coe_sort T (fun P => (R₀ P : ℂ))
      _ = ((∏ P ∈ T, R₀ P : ℂˣ) : ℂ) := (Units.coe_prod R₀ T).symm
  have hC : (∏ P ∈ T, ∏ Q ∈ T,
      z P Q ^ ((A P : ℤ) * k Q + ((A P : ℤ) - k P) * A Q + 2 * (c.val P : ℤ) * c.val Q)) = 1 := by
    calc
      _ = ∏ P ∈ T, ∏ Q ∈ T, sourceCombinedCrossUnit F hζ S₀ c.val l k P Q := by
        apply Finset.prod_congr rfl
        intro P _
        apply Finset.prod_congr rfl
        intro Q _
        simp only [A, z, sourceCombinedCrossUnit, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
          Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      _ = 1 := sourceCombinedCrossUnit_finite F hζ S₀ c.val l k T
  have hU : (∏ P ∈ T, ∏ Q ∈ T, z P Q ^ (2 * c.val P * c.val Q)) *
      (∏ P ∈ T, R₀ P) = ∏ P ∈ T, W P := by
    have h := sourceDirectedProduct_with_gauss T z θ c.val k A
    rw [hC, mul_one] at h
    exact h
  change _ * (∏ P : T, sourceExponentCRTUnitFactor F S₀ hζ
    (reflectionPrimeCharacters F hζ S₀) k A r u hu T P) = ∏ P : T, (W P.val : ℂ)
  rw [hΓ, hF, ← Units.val_mul, hU, Units.coe_prod]
  exact (Finset.prod_coe_sort T (fun P => (W P : ℂ))).symm

end
end ArtinMatthews.SourceEulerAssembly
