module

public import ArtinMatthews.KummerRowField
public import ArtinMatthews.ArtinFrobeniusIdealCharacter
public import ArtinMatthews.EisensteinAngularCyclotomic
public import ArtinMatthews.ProbeAngularResidueSymbol
public import ArtinMatthews.SourceAngularEmbedding
public import Mathlib.RingTheory.Henselian
public import ArtinMatthews.SourceAngularResidueValue
public import ArtinMatthews.SourceFrobeniusIntegralUnit
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

/-! Genuine Frobenius value after scaling a Kummer root to an integral
radicand. The scaling cancels in the automorphism ratio. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AlgebraicNumberTheory.PowerResidueSymbols
open AngularLambda VaryingKummerAnalytic
open OAI OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F] {ζ : F}

omit [NumberField F] in
theorem sourcePrimitiveSix (hζ : IsPrimitiveRoot ζ 12) : IsPrimitiveRoot (ζ ^ 2) 6 := by
  simpa using hζ.pow_of_dvd (p := 2) (by decide) (by decide)

theorem sourceComplexEmbedding_primeResidue (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 F)) (hsix : (6 : 𝓞 F) ∉ P.asIdeal)
    (hmu : (primitiveRoots 6 F).Nonempty) (a : 𝓞 F) (ha : a ∉ P.asIdeal) :
    sourceComplexEmbedding hζ
        (((primeIdealPowerResidueSymbol F P 6 hmu (probePrimeNorm_coprime_six F P hsix)
          a ha : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F) =
      cyclotomicAngularResidueCharacter hζ P hsix (Ideal.Quotient.mk P.asIdeal a) := by
  let : Algebra BaseField F := baseAlgebraOfTwelve hζ
  let u := primeIdealResidueUnit F P a ha
  have hr := probeAngularIntegralCharacter_eq_symbol F P hsix hmu a ha
  have hr' : probeIntegralSixthRoot F (probeAngularIntegralCharacter F P hsix u)
      (probeAngularIntegralCharacter_pow_six F P hsix u) =
      (primeIdealPowerResidueSymbol F P 6 hmu (probePrimeNorm_coprime_six F P hsix)
        a ha : rootsOfUnity 6 (𝓞 F)) := hr
  have hv := congrArg (fun z : rootsOfUnity 6 (𝓞 F) =>
    sourceComplexEmbedding hζ (((z : (𝓞 F)ˣ) : 𝓞 F) : F)) hr'
  change sourceComplexEmbedding hζ
      ((algebraMap BaseIntegers (𝓞 F) (probeAngularIntegralCharacter F P hsix u) : 𝓞 F) : F) = _ at hv
  apply hv.symm.trans
  apply (sourceComplexEmbedding_baseInteger hζ _).trans
  symm
  change globalAngularResidueCharacter F P hsix (Ideal.Quotient.mk P.asIdeal a) = _
  simpa only [u, primeIdealResidueUnit, Units.val_mk0] using
    (probeAngularIntegralCharacter_complex F P hsix (u : 𝓞 F ⧸ P.asIdeal))

theorem sourceRowFrobenius_scaled (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 F)) (hsix : (6 : 𝓞 F) ∉ P.asIdeal)
    (u : Fˣ) (b a : 𝓞 F) (hb : b ≠ 0) (ha : a ∉ P.asIdeal)
    (hab : (u : F) * (b : F) ^ 6 = (a : F)) :
    letI : Algebra F ℂ := sourceComplexAlgebra hζ
    (sixthKummerRowCharacter (sourcePrimitiveSix F hζ)
      {((u : F))} (u : F) (Finset.mem_singleton_self _) u.ne_zero
      (GaloisIdealCharacter.primeFrobenius F (sixthKummerRowField {((u : F))}) P) : ℂ) =
      cyclotomicAngularResidueCharacter hζ P hsix (Ideal.Quotient.mk P.asIdeal a) := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let A : Finset F := {((u : F))}
  let E := sixthKummerRowField A
  let r : E := sixthKummerRowRoot A (u : F) (Finset.mem_singleton_self _)
  let bE : E := algebraMap F E (b : F)
  let β := r * bE
  have hbF : (b : F) ≠ 0 := by exact_mod_cast hb
  have hbE : bE ≠ 0 := by
    simpa only [map_zero] using (algebraMap F E).injective.ne hbF
  have hr : r ^ 6 = algebraMap F E (u : F) :=
    sixthKummerRowRoot_pow A (u : F) (Finset.mem_singleton_self _)
  have hβ : β ^ 6 = algebraMap F E (a : F) := by
    dsimp only [β, bE]
    rw [mul_pow, hr, ← map_pow, ← map_mul, hab]
  let σ := GaloisIdealCharacter.primeFrobenius F E P
  have hRatio : σ β / β = σ r / r := by
    dsimp only [β, bE]
    rw [map_mul, AlgEquiv.commutes, mul_div_mul_right _ _ hbE]
  have hmu : (primitiveRoots 6 F).Nonempty :=
    ⟨ζ ^ 2, (mem_primitiveRoots (by decide : 0 < 6)).mpr (sourcePrimitiveSix F hζ)⟩
  have hf := frobenius_sixthRoot_integralUnit F E P hsix hmu
    (probePrimeNorm_coprime_six F P hsix) a ha β hβ
  change σ β / β = _ at hf
  rw [hRatio] at hf
  change ((σ r / r : E) : ℂ) = _
  calc
    _ = sourceComplexEmbedding hζ
        (((primeIdealPowerResidueSymbol F P 6 hmu (probePrimeNorm_coprime_six F P hsix)
          a ha : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F) :=
      congrArg (fun x : E => (x : ℂ)) hf
    _ = _ := sourceComplexEmbedding_primeResidue F hζ P hsix hmu a ha

end
end ArtinMatthews
