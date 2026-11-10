module

public import ArtinMatthews.SourceAngularEmbedding
public import ArtinMatthews.KummerFrobeniusResidue
public import ArtinMatthews.ProbeAngularResidueSymbol
public import ArtinMatthews.EisensteinAngularCyclotomic
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

/-! The actual complex image of the canonical prime residue symbol
agrees with the oriented angular character, for the explicitly constructed
extension of the Eisenstein embedding. -/

namespace ArtinMatthews.AngularLambda

open NumberField IsDedekindDomain
open AlgebraicNumberTheory.PowerResidueSymbols
open VaryingKummerAnalytic
open OAI OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT
open scoped NumberField Classical

noncomputable section

variable {F : Type} [Field F] [NumberField F] {ζ : F}

theorem sourceComplexEmbedding_baseInteger (hζ : IsPrimitiveRoot ζ 12) (b : BaseIntegers) :
    letI : Algebra BaseField F := baseAlgebraOfTwelve hζ
    sourceComplexEmbedding hζ ((algebraMap BaseIntegers (𝓞 F) b : 𝓞 F) : F) =
      eisEmbedding b := by
  let : Algebra BaseField F := baseAlgebraOfTwelve hζ
  change sourceComplexEmbedding hζ
    (algebraMap (𝓞 F) F (algebraMap BaseIntegers (𝓞 F) b)) = _
  rw [← IsScalarTower.algebraMap_apply BaseIntegers (𝓞 F) F,
    IsScalarTower.algebraMap_apply BaseIntegers BaseField F,
    sourceComplexEmbedding_base, baseComplexEmbedding_integer]

theorem sourceComplexEmbedding_fourResidue (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 F)) (hsix : (6 : 𝓞 F) ∉ P.asIdeal)
    (hmu : (primitiveRoots 6 F).Nonempty) :
    sourceComplexEmbedding hζ
        (((primeIdealPowerResidueSymbol F P 6 hmu (probePrimeNorm_coprime_six F P hsix)
          4 (four_not_mem_of_six_not_mem F P hsix) : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F) =
      cyclotomicAngularResidueCharacter hζ P hsix (4 : 𝓞 F ⧸ P.asIdeal) := by
  let : Algebra BaseField F := baseAlgebraOfTwelve hζ
  let u := primeIdealResidueUnit F P (4 : 𝓞 F) (four_not_mem_of_six_not_mem F P hsix)
  have hr := probeAngularIntegralCharacter_eq_symbol F P hsix hmu
    (4 : 𝓞 F) (four_not_mem_of_six_not_mem F P hsix)
  have hr' : probeIntegralSixthRoot F (probeAngularIntegralCharacter F P hsix u)
      (probeAngularIntegralCharacter_pow_six F P hsix u) =
      (primeIdealPowerResidueSymbol F P 6 hmu (probePrimeNorm_coprime_six F P hsix)
        4 (four_not_mem_of_six_not_mem F P hsix) : rootsOfUnity 6 (𝓞 F)) := hr
  have hv := congrArg (fun z : rootsOfUnity 6 (𝓞 F) =>
    sourceComplexEmbedding hζ (((z : (𝓞 F)ˣ) : 𝓞 F) : F)) hr'
  change sourceComplexEmbedding hζ
      ((algebraMap BaseIntegers (𝓞 F) (probeAngularIntegralCharacter F P hsix u) : 𝓞 F) : F) = _ at hv
  apply hv.symm.trans
  apply (sourceComplexEmbedding_baseInteger hζ _).trans
  symm
  change globalAngularResidueCharacter F P hsix 4 = _
  simpa only [u, primeIdealResidueUnit, Units.val_mk0, map_ofNat] using
    (probeAngularIntegralCharacter_complex F P hsix (u : 𝓞 F ⧸ P.asIdeal))

end

end ArtinMatthews.AngularLambda
