module

public import ArtinMatthews.SourceActualCrossCancellation
public import ArtinMatthews.SourceDirectedUnitProducts
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

/-! The actual finite frame underlying the source cofactor products.
Every frame is obtained by restricting the fixed exterior generators. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open SIntegerPrincipalization SIntegerQuotient SourceCRTNormalization
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (T : Finset (SourceExteriorPrime F S₀))

local notation "seed" => sourceHilbertSeed F S₀

def sourceFramePrime (i : T) : HeightOneSpectrum (𝓞 F) := i.val.val

theorem sourceFramePrime_pairwise : Pairwise fun i j : T => sourceFramePrime F S₀ T i ≠ sourceFramePrime F S₀ T j := by
  intro i j hij he
  exact hij (Subtype.ext (Subtype.ext he))

theorem sourceFramePrime_exterior (i : T) : sourceFramePrime F S₀ T i ∉ principalizingSet seed :=
  i.val.property

def sourceFrameGenerator (i : T) : PrincipalIntegerRing seed := sourceAllowedPrimeGenerator F hζ S₀ i.val

theorem sourceFrameGenerator_ideal (i : T) :
    (sourceFramePrime F S₀ T i).asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing seed)) =
      Ideal.span {sourceFrameGenerator F hζ S₀ T i} :=
  sourceAllowedPrimeGenerator_ideal F hζ S₀ i.val

def sourceFrameCharacter (i : T) : MulChar ((𝓞 F) ⧸ (sourceFramePrime F S₀ T i).asIdeal) ℂ :=
  reflectionPrimeCharacters F hζ S₀ i.val

def sourceFrameDirectedUnit (i j : T) : ℂˣ :=
  sourceDirectedCharacterUnit F seed (sourceFramePrime F S₀ T)
    (sourceFramePrime_pairwise F S₀ T) (sourceFramePrime_exterior F S₀ T)
    (sourceFrameGenerator F hζ S₀ T) (sourceFrameGenerator_ideal F hζ S₀ T)
    (sourceFrameCharacter F hζ S₀ T) i j

theorem sourceFrameDirectedUnit_eq (i j : T) :
    sourceFrameDirectedUnit F hζ S₀ T i j = sourcePrimeCrossDiagonalUnit F hζ S₀ i.val j.val := by
  by_cases h : i = j
  · subst j
    unfold sourceFrameDirectedUnit
    rw [sourceDirectedCharacterUnit_diag, sourcePrimeCrossDiagonalUnit_diag]
  · have hv : i.val ≠ j.val := fun he => h (Subtype.ext he)
    apply Units.ext
    unfold sourceFrameDirectedUnit
    rw [sourceDirectedCharacterUnit_val F seed _ _ _ _ _ _ i j h,
      sourcePrimeCrossDiagonalUnit, dite_eq_right hv, sourcePrimeCrossUnit_val]
    rfl

def sourceFrameCofactorCharacter (e : SourcePrimeExponents F S₀) (i : T) : ℂˣ :=
  sourceCharacterUnit seed (sourceFramePrime F S₀ T i) (sourceFramePrime_exterior F S₀ T i)
    (sourceFrameGenerator F hζ S₀ T i) (sourceFrameGenerator_ideal F hζ S₀ T i)
    (sourceFrameCharacter F hζ S₀ T i)
    (sourcePrimeCofactor seed (sourceFrameGenerator F hζ S₀ T) (fun j => e j.val) i)
    (sourcePrimeCofactor_not_mem seed (sourceFramePrime F S₀ T)
      (sourceFramePrime_pairwise F S₀ T) (sourceFramePrime_exterior F S₀ T)
      (sourceFrameGenerator F hζ S₀ T) (sourceFrameGenerator_ideal F hζ S₀ T)
      (fun j => e j.val) i)

theorem sourceFrameCofactorCharacter_prod (e : SourcePrimeExponents F S₀) (i : T) :
    sourceFrameCofactorCharacter F hζ S₀ T e i =
      ∏ Q ∈ T, sourcePrimeCrossDiagonalUnit F hζ S₀ i.val Q ^ e Q := by
  calc
    _ = ∏ j ∈ Finset.univ.erase i, sourceFrameDirectedUnit F hζ S₀ T i j ^ e j.val :=
      sourceCharacterUnit_cofactor F seed _ _ _ _ _ _ _ i
    _ = ∏ j ∈ Finset.univ.erase i, sourcePrimeCrossDiagonalUnit F hζ S₀ i.val j.val ^ e j.val := by
      apply Finset.prod_congr rfl
      intro j _
      rw [sourceFrameDirectedUnit_eq]
    _ = ∏ j : T, sourcePrimeCrossDiagonalUnit F hζ S₀ i.val j.val ^ e j.val := by
      apply Finset.prod_erase
      rw [sourcePrimeCrossDiagonalUnit_diag, one_pow]
    _ = _ := Finset.prod_coe_sort T (fun Q => sourcePrimeCrossDiagonalUnit F hζ S₀ i.val Q ^ e Q)

end
end ArtinMatthews.SourceEulerAssembly
