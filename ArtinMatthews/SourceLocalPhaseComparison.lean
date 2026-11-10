module

public import ArtinMatthews.ReflectionGaussPrefix
public import ArtinMatthews.SourceThetaLocal
public import ArtinMatthews.ProbeIdealCyclotomicSource
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaFourier
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

/-! The standard generator phase and the independently chosen trace
phase are related by a genuine residue unit. The unit is kept in each
Gauss coefficient. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open SIntegerFourier AngularLambda OAI.SevenEighths
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (P : SourceExteriorPrime F S₀)

local notation "κ" => ((𝓞 F) ⧸ P.val.asIdeal)
local notation "χ" => reflectionPrimeCharacters F hζ S₀ P
local instance sourcePhaseField : Field κ := Ideal.Quotient.field _
local instance sourcePhaseFinite : Finite κ := Ring.HasFiniteQuotients.finiteQuotient P.val.ne_bot
local instance sourcePhaseFintype : Fintype κ := Fintype.ofFinite _

theorem sourcePrimeCharacter_order : orderOf χ = 6 :=
  cyclotomicAngularResidueCharacter_order hζ P.val (source_exterior_six_not_mem F S₀ P.val P.property)

theorem sourcePrimeCharacter_minus_one : χ (-1) = 1 :=
  probeIdealCharacter_minus_one_of_twelve hζ P.val χ (sourcePrimeCharacter_order F hζ S₀ P)

theorem sourcePrimeCharacter_unit_pow_six (a : κˣ) : (χ a) ^ 6 = 1 := by
  rw [← MulChar.pow_apply_coe, (orderOf_dvd_iff_pow_eq_one).mp (by
    rw [sourcePrimeCharacter_order F hζ S₀ P]), MulChar.one_apply_coe]

theorem sourcePrimeResidue_char_ne_two : ringChar κ ≠ 2 :=
  probeIdealResidue_char_ne_two P.val (source_exterior_six_not_mem F S₀ P.val P.property)

theorem sourcePrimeResiduePhase_exists_mulShift
    (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀) :
    ∃ a : κˣ, sourcePrimeResiduePhase F hζ S₀ P =
      (probeIdealResiduePhase F P.val).mulShift a := by
  obtain ⟨a, ha⟩ := (primitive_addChar_mulShift_bijective
    (probeIdealResiduePhase F P.val) (probeIdealResiduePhase_primitive F P.val)).surjective
      (sourcePrimeResiduePhase F hζ S₀ P)
  have ha0 : a ≠ 0 := by
    intro h
    have hp := sourcePrimeResiduePhase_primitive F hζ S₀ hS P (one_ne_zero : (1 : κ) ≠ 0)
    apply hp
    rw [AddChar.mulShift_one, ← ha, h, AddChar.mulShift_zero]
  exact ⟨Units.mk0 a ha0, ha.symm⟩

def sourcePrimeTau (ψ : MulChar κ ℂ) : ℂ :=
  residueSourceTau (sourceHilbertSeed F S₀) P.val P.property
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) ψ

theorem sourcePrimeTau_mulShift (a : κˣ)
    (ha : sourcePrimeResiduePhase F hζ S₀ P = (probeIdealResiduePhase F P.val).mulShift a)
    (v : ℕ) :
    sourcePrimeTau F hζ S₀ P (χ ^ v) = (χ a)⁻¹ ^ v * probeIdealTau F P.val (χ ^ v) := by
  simp only [sourcePrimeTau, residueSourceTau, probeIdealTau, tsum_fintype]
  change gaussSum (χ ^ v) (sourcePrimeResiduePhase F hζ S₀ P) =
    (χ a)⁻¹ ^ v * gaussSum (χ ^ v) (probeIdealResiduePhase F P.val)
  rw [ha, gaussSum_mulShift_eq, MulChar.inv_apply_eq_inv', MulChar.pow_apply_coe, inv_pow]

theorem sourcePrimeGaussGamma_eq_tau (v : ℕ) :
    probeGaussGamma χ (sourcePrimeResiduePhase F hζ S₀ P) v =
      sourcePrimeTau F hζ S₀ P (χ ^ v) / (Real.sqrt (Ideal.absNorm P.val.asIdeal : ℝ) : ℂ) := by
  have hc : Fintype.card κ = Ideal.absNorm P.val.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  simp only [sourcePrimeTau, residueSourceTau, probeGaussGamma, ProbeGauss.normalizedGauss,
    gaussSum, tsum_fintype, hc]
  rfl

theorem sourcePrimeGaussGamma_mulShift (a : κˣ)
    (ha : sourcePrimeResiduePhase F hζ S₀ P = (probeIdealResiduePhase F P.val).mulShift a)
    (v : ℕ) :
    probeGaussGamma χ (sourcePrimeResiduePhase F hζ S₀ P) v =
      (χ a)⁻¹ ^ v * probeIdealGaussGamma F P.val χ v := by
  rw [sourcePrimeGaussGamma_eq_tau, sourcePrimeTau_mulShift F hζ S₀ P a ha v,
    probeIdealGaussGamma, mul_div_assoc]

theorem sourceNormalizedPrimeGamma_mulShift (a : κˣ)
    (ha : sourcePrimeResiduePhase F hζ S₀ P = (probeIdealResiduePhase F P.val).mulShift a) :
    reflectionNormalizedPrimeGamma F hζ S₀ P =
      (χ a)⁻¹ ^ 2 * probeIdealGaussGamma F P.val χ 2 := by
  change sourcePrimeTau F hζ S₀ P (χ ^ 2) / _ = _
  rw [← sourcePrimeGaussGamma_eq_tau]
  exact sourcePrimeGaussGamma_mulShift F hζ S₀ P a ha 2

end
end ArtinMatthews.SourceEulerAssembly
