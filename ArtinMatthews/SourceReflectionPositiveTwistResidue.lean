module

public import ArtinMatthews.SIntegerAdicResidueMap
public import ArtinMatthews.ReflectionCoefficientRow
public import ArtinMatthews.SourceJacquetHaar
public import ArtinMatthews.SourceJacquetActualShell
public import ArtinMatthews.SourceLocalKernelCoefficient
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

/-! The completed residue is the original S-integer residue at every
exterior prime. Reduce character powers in the character monoid so
that a positive multiple of six retains the zero extension. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open SIntegerQuotient SIntegerAdicResidue VaryingKummerAnalytic QuadraticWeil
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open scoped NumberField Classical BigOperators ValuativeRel

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "R" => (𝓞 K) ⧸ P.val.asIdeal
local notation "L" => P.val.adicCompletion K
local notation "OS" => sourceRing K S₀
local notation "I" => sourceJacquetIntegers K P.val
local notation "red" => sourceJacquetReduction K P.val
local notation "T" => sourceHilbertSeed K S₀
local notation "p" => sourceAllowedPrimeGenerator K hζ S₀ P
local notation "hp" => sourceAllowedPrimeGenerator_ideal K hζ S₀ P
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P

local instance positiveResidueAdicRelation : ValuativeRel L := adicRelation K P.val

local instance positiveResidueAdicLocalField : IsNonarchimedeanLocalField L := adicLocalField K P.val

def sourceReflectionPositiveSIntegerAt (x : OS) : I :=
  let a := adicIntegralOfSInteger K T P.val P.property x
  ⟨(a : L), a.property⟩

theorem sourceReflectionPositiveSIntegerAt_val (x : OS) :
    (sourceReflectionPositiveSIntegerAt K S₀ P x : L) = algebraMap K L (x : K) := rfl

theorem sourceReflectionPositiveSIntegerAt_reduce (x : OS) :
    red (sourceReflectionPositiveSIntegerAt K S₀ P x) =
      generatorResidueEquiv T P.val P.property p hp (Ideal.Quotient.mk _ x) := by
  change (adicIntegerResidueEquiv K P.val).symm (adicResidueOfSInteger K T P.val P.property x) = _
  let E := adicIntegerResidueEquiv K P.val
  exact (congrArg E.symm (adicResidueOfSInteger_generator_compare K T P.val P.property p hp x)).trans
    (E.symm_apply_apply _)

theorem sourceReflectionPositiveSIntegerAt_reduce_eq_zero_iff (x : OS) :
    red (sourceReflectionPositiveSIntegerAt K S₀ P x) = 0 ↔
      x ∈ P.val.asIdeal.map (algebraMap (𝓞 K) OS) := by
  change (adicIntegerResidueEquiv K P.val).symm (adicResidueOfSInteger K T P.val P.property x) = 0 ↔ _
  rw [← map_zero (adicIntegerResidueEquiv K P.val).symm, (adicIntegerResidueEquiv K P.val).symm.injective.eq_iff]
  exact adicResidueOfSInteger_eq_zero_iff K T P.val P.property x

def sourceReflectionPositiveIndex (n : ℕ) : Fin 6 :=
  ⟨n % 6, Nat.mod_lt n (by decide)⟩

theorem sourceReflectionPositiveLocalWeight_eq (n : ℕ) (hn : 0 < n) (x : OS) :
    (χ₀ ^ (sourceReflectionPositiveIndex n).val : MulChar R ℂ)
      (red (sourceReflectionPositiveSIntegerAt K S₀ P x)) =
      sourcePrimeExponentLocalWeight K hζ S₀ (reflectionPrimeCharacters K hζ S₀) P n x := by
  have he := pow_mod_orderOf χ₀ n
  rw [sourceJacquetActualCharacter_order K hζ S₀ P] at he
  rw [sourceReflectionPositiveIndex, he, sourceReflectionPositiveSIntegerAt_reduce K hζ S₀ P]
  let b : OS := p
  let I₀ : Ideal OS := Ideal.span {b^n}
  let hI := generator_power_ideal T P.val b hp n
  have hq : (Ideal.quotEquivOfEq hI) (Ideal.Quotient.mk (primePowerIdeal T P.val n) x) =
      Ideal.Quotient.mk I₀ x := Ideal.quotEquivOfEq_mk hI x
  change (χ₀ ^ n : MulChar R ℂ) (generatorResidueEquiv T P.val P.property b hp
      (Ideal.Quotient.mk _ x)) =
    generatorPowerWeight T P.val P.property b hp χ₀ n
      ((Ideal.quotEquivOfEq hI) (Ideal.Quotient.mk (primePowerIdeal T P.val n) x))
  rw [hq]
  change _ = if h : 0 < n then
    (generatorResidueCharacter T P.val P.property b hp χ₀ ^ n)
      (generatorResidueReduction T b n h (Ideal.Quotient.mk I₀ x)) else 1
  rw [dite_eq_left hn]
  let z := Ideal.Quotient.mk (Ideal.span {b} : Ideal OS) x
  have hred : generatorResidueReduction T b n hn (Ideal.Quotient.mk I₀ x) = z :=
    generatorResidueReduction_mk T b n hn x
  calc
    _ = generatorResidueCharacter T P.val P.property b hp (χ₀ ^ n) z := rfl
    _ = (generatorResidueCharacter T P.val P.property b hp χ₀ ^ n) z :=
      congrArg (fun c : MulChar (OS ⧸ Ideal.span {b}) ℂ => c z)
        (SourceCRTNormalization.generatorResidueCharacter_pow T P.val P.property b hp χ₀ n).symm
    _ = _ := congrArg (generatorResidueCharacter T P.val P.property b hp χ₀ ^ n) hred.symm

end
end ArtinMatthews
