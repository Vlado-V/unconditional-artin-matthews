module

public import ArtinMatthews.SourceUnitWeightValues
public import ArtinMatthews.SourceLocalUnits
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ArtinMatthews.AllowedGeneratorBase
import ArtinMatthews.EisensteinAngularIdeal


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine source residue units: multiplication/powers, and the sixth
power of the actual angular residue character on every local unit. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic AngularLambda
open SIntegerPrincipalization SIntegerQuotient SIntegerResidueSymbol SourceCRTNormalization
open scoped NumberField Classical
noncomputable section
variable {F : Type} [Field F] [NumberField F]
variable (T : Finset (HeightOneSpectrum (𝓞 F)))
variable (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ principalizingSet T)
variable (a : PrincipalIntegerRing T)
variable (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T)) = Ideal.span {a})
variable (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ)

include hP ha in
theorem sourcePrimeUnit_mul_not_mem (x y : PrincipalIntegerRing T)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T)))
    (hy : y ∉ P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T))) :
    x * y ∉ P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T)) := by
  have hp : (P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T))).IsPrime := by
    rw [ha]
    exact (sourceGenerator_maximal T P hP a ha).isPrime
  intro hm
  exact (hp.mem_or_mem hm).elim hx hy

include hP ha in
theorem sourcePrimeUnit_pow_not_mem (x : PrincipalIntegerRing T)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T))) (n : ℕ) :
    x ^ n ∉ P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T)) := by
  have hp : (P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T))).IsPrime := by
    rw [ha]
    exact (sourceGenerator_maximal T P hP a ha).isPrime
  exact fun hm => hx (hp.mem_of_pow_mem n hm)

theorem sourceCharacterUnit_mul_actual (x y : PrincipalIntegerRing T)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T)))
    (hy : y ∉ P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T)))
    (hxy : x * y ∉ P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T))) :
    sourceCharacterUnit T P hP a ha χ (x * y) hxy =
      sourceCharacterUnit T P hP a ha χ x hx * sourceCharacterUnit T P hP a ha χ y hy := by
  apply Units.ext
  simp only [Units.val_mul, sourceCharacterUnit_val, map_mul]

theorem sourceCharacterUnit_pow_actual (x : PrincipalIntegerRing T)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T))) (n : ℕ)
    (hxn : x ^ n ∉ P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T))) :
    sourceCharacterUnit T P hP a ha χ (x ^ n) hxn =
      sourceCharacterUnit T P hP a ha χ x hx ^ n := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, sourceCharacterUnit_val, map_pow]

theorem sourceCharacterUnit_pow_six_of_order (hχ : orderOf χ = 6)
    (x : PrincipalIntegerRing T)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T))) :
    sourceCharacterUnit T P hP a ha χ x hx ^ (6 : ℕ) = 1 := by
  let u := sIntegerResidueUnit F T P hP a ha x hx
  have hp := pow_orderOf_eq_one χ
  rw [hχ] at hp
  have hv := congrArg (fun θ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ => θ u) hp
  apply Units.ext
  simpa only [sourceCharacterUnit, Units.val_pow_eq_pow_val, Units.val_one,
    MulChar.coe_toUnitHom, MulChar.pow_apply_coe, MulChar.one_apply_coe, u] using hv

end
end ArtinMatthews.SourceEulerAssembly
