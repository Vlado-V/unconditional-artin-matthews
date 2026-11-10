module

public import ArtinMatthews.IdealPrimeWeilSquareSum
public import ArtinMatthews.AdicPrimeQuadraticGaussian
public import ArtinMatthews.FiniteGeneratorGaussSign
public import ArtinMatthews.PrimeResidueNegOneSquare
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! The arbitrary-generator local analytic Weil factor equals the genuine
negative-source sextic cubic Gauss factor. The sign at -1 is explicit in
general and is derived to be one from an actual primitive twelfth root. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ArtinMatthews.QuadraticGauss
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField ValuativeRel Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local instance sexticWeilRelation : ValuativeRel (v.adicCompletion F) := adicRelation F v
local instance sexticWeilLocalField : IsNonarchimedeanLocalField (v.adicCompletion F) := adicLocalField F v
local instance sexticWeilMeasurable : MeasurableSpace (v.adicCompletion F) := borel (v.adicCompletion F)
local instance sexticWeilBorel : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance sexticWeilQuotientField : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
local instance sexticWeilQuotientFinite : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
local instance sexticWeilQuotientFintype : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
local instance sexticWeilResidueFintype : Fintype 𝓀[v.adicCompletion F] := Fintype.ofFinite _

theorem idealResidue_char_ne_two
    (h2 : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) 2 = 1) :
    ringChar (𝓞 F ⧸ v.asIdeal) ≠ 2 := by
  let : Algebra (𝓞 F ⧸ v.asIdeal) 𝓀[v.adicCompletion F] := (adicIntegerResidueEquiv F v).toRingHom.toAlgebra
  have he : ringChar (𝓞 F ⧸ v.asIdeal) = ringChar 𝓀[v.adicCompletion F] := Algebra.ringChar_eq _ _
  rw [he]
  exact tameResidue_char_ne_two (v.adicCompletion F) (adic_canonical_two_unit F v h2)

theorem adicPrimeUnit_normalizedWeil_eq_negativeSexticGamma
    (ψ : AddChar (v.adicCompletion F) ℂ) (hψ : adicConductorZero F v ψ)
    (a : (v.adicCompletion F)ˣ)
    (ha : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (a : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (hunit : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ)
    (h2 : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) 2 = 1)
    (χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ) (hχ : orderOf χ = 6) :
    analyticNormalizedWeil ψ a⁻¹ = residueCharacter (𝓞 F ⧸ v.asIdeal) (-1) *
      probeGaussGamma χ ((idealPrimeResidueChar F v ψ hψ (a : v.adicCompletion F) ha).mulShift (-1)) 3 := by
  have hSquare := adicPrimeUnit_normalizedWeil_eq_idealSquareSum F v ψ hψ a ha hunit hc h2
  have hFinite := positiveSquareSum_eq_negativeSexticGamma (𝓞 F ⧸ v.asIdeal)
    (idealResidue_char_ne_two F v h2) χ hχ _ (idealPrimeResidueChar_nontrivial F v ψ hψ _ ha)
  have hcard : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [hcard] at hFinite
  exact hSquare.trans hFinite

theorem adicPrimeUnit_normalizedWeil_eq_negativeSexticGamma_of_twelve {ζ : F}
    (hζ : IsPrimitiveRoot ζ 12)
    (ψ : AddChar (v.adicCompletion F) ℂ) (hψ : adicConductorZero F v ψ)
    (a : (v.adicCompletion F)ˣ)
    (ha : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (a : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (hunit : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ)
    (h2 : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) 2 = 1)
    (χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ) (hχ : orderOf χ = 6) :
    analyticNormalizedWeil ψ a⁻¹ =
      probeGaussGamma χ ((idealPrimeResidueChar F v ψ hψ (a : v.adicCompletion F) ha).mulShift (-1)) 3 := by
  rw [adicPrimeUnit_normalizedWeil_eq_negativeSexticGamma F v ψ hψ a ha hunit hc h2 χ hχ,
    residueCharacter_neg_one_of_isSquare (𝓞 F ⧸ v.asIdeal) (idealResidue_neg_one_square_of_twelve F v hζ), one_mul]

theorem sexticIdealCharacter_neg_one_of_twelve {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ) (hχ : orderOf χ = 6) : χ (-1) = 1 :=
  sexticCharacter_neg_one_of_isSquare (𝓞 F ⧸ v.asIdeal) χ hχ (idealResidue_neg_one_square_of_twelve F v hζ)

end

end ArtinMatthews.QuadraticWeil
