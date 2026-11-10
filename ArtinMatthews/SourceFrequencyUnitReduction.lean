module

public import ArtinMatthews.SourceGeneratorCofactor
public import ArtinMatthews.ReflectionCoefficientRow
public import ArtinMatthews.SourceExponentFiniteFactor
public import ArtinMatthews.SourceUnitWeightValues
public import ArtinMatthews.SourceCharacterSixth
public import ArtinMatthews.SourcePrimeExponentProducts
public import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The frequency cofactor is the actual cofactor of u times a sixth
power of an omitted generator product. Its residue character therefore
depends only on u, not on the other prime coordinates of r. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic AngularLambda
open SIntegerPrincipalization SIntegerQuotient SourceCRTNormalization
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "R" => sourceRing F S₀
local notation "seed" => sourceHilbertSeed F S₀

def sourcePrimeCharacterUnit (P : SourceExteriorPrime F S₀) (x : R)
    (hx : x ∉ P.val.asIdeal.map (algebraMap (𝓞 F) R)) : ℂˣ :=
  sourceCharacterUnit seed P.val P.property (sourceAllowedPrimeGenerator F hζ S₀ P)
    (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) (reflectionPrimeCharacters F hζ S₀ P) x hx

theorem sourcePrimeCharacterUnit_congr (P : SourceExteriorPrime F S₀) {x y : R}
    (hx : x ∉ P.val.asIdeal.map (algebraMap (𝓞 F) R))
    (hy : y ∉ P.val.asIdeal.map (algebraMap (𝓞 F) R)) (he : x = y) :
    sourcePrimeCharacterUnit F hζ S₀ P x hx = sourcePrimeCharacterUnit F hζ S₀ P y hy := by
  subst y
  rfl

theorem sourcePrimeCharacterUnit_pow_six (P : SourceExteriorPrime F S₀) (x : R)
    (hx : x ∉ P.val.asIdeal.map (algebraMap (𝓞 F) R)) :
    sourcePrimeCharacterUnit F hζ S₀ P x hx ^ (6 : ℕ) = 1 :=
  sourceCharacterUnit_pow_six_of_order seed P.val P.property _
    (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) _
    (cyclotomicAngularResidueCharacter_order hζ P.val
      (source_exterior_six_not_mem F S₀ P.val P.property)) x hx

theorem sourceFrequencyCofactor_base (u : R) (hu : u ≠ 0) (P : SourceExteriorPrime F S₀) :
    u = sourceAllowedPrimeGenerator F hζ S₀ P ^ sourceElementExponents F S₀ u hu P *
      sourceFrequencyCofactor F S₀ hζ u hu 0 P := by
  simpa only [sourcePrimeExponentGenerator_zero, one_pow, mul_one, Finsupp.zero_apply,
    mul_zero, add_zero] using (sourceFrequencyCofactor_spec F S₀ hζ u hu 0 P).1

theorem sourceFrequencyCofactor_mul_sixth (u : R) (hu : u ≠ 0)
    (r : SourcePrimeExponents F S₀) (P : SourceExteriorPrime F S₀) :
    sourceFrequencyCofactor F S₀ hζ u hu r P =
      sourceFrequencyCofactor F S₀ hζ u hu 0 P * sourceGeneratorCofactor F hζ S₀ r P ^ 6 := by
  let a := sourceAllowedPrimeGenerator F hζ S₀ P
  let j := sourceElementExponents F S₀ u hu P
  let x := sourceFrequencyCofactor F S₀ hζ u hu 0 P
  let y := sourceGeneratorCofactor F hζ S₀ r P
  apply mul_left_cancel₀ (a := a ^ (j + 6 * r P))
    (pow_ne_zero _ (sourceAllowedPrimeGenerator_ne_zero F hζ S₀ P))
  calc
    _ = u * sourcePrimeExponentGenerator F hζ S₀ r ^ 6 :=
      (sourceFrequencyCofactor_spec F S₀ hζ u hu r P).1.symm
    _ = (a ^ j * x) * (a ^ r P * y) ^ 6 := congrArg₂ (fun b c : R => b * c ^ 6)
      (sourceFrequencyCofactor_base F hζ S₀ u hu P) (sourceGeneratorCofactor_factor F hζ S₀ r P)
    _ = a ^ (j + 6 * r P) * (x * y ^ 6) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm (r P) 6, pow_add]
      exact mul_mul_mul_comm _ _ _ _

def sourceResidualCharacterUnit (u : R) (hu : u ≠ 0) (P : SourceExteriorPrime F S₀) : ℂˣ :=
  sourcePrimeCharacterUnit F hζ S₀ P (sourceFrequencyCofactor F S₀ hζ u hu 0 P)
    (sourceFrequencyCofactor_spec F S₀ hζ u hu 0 P).2

theorem sourceFrequencyCharacterUnit_eq (u : R) (hu : u ≠ 0)
    (r : SourcePrimeExponents F S₀) (P : SourceExteriorPrime F S₀) :
    sourcePrimeCharacterUnit F hζ S₀ P (sourceFrequencyCofactor F S₀ hζ u hu r P)
        (sourceFrequencyCofactor_spec F S₀ hζ u hu r P).2 =
      sourceResidualCharacterUnit F hζ S₀ u hu P := by
  let x := sourceFrequencyCofactor F S₀ hζ u hu 0 P
  let y := sourceGeneratorCofactor F hζ S₀ r P
  have hx := (sourceFrequencyCofactor_spec F S₀ hζ u hu 0 P).2
  have hy := sourceGeneratorCofactor_not_mem F hζ S₀ r P
  have hy6 : y ^ 6 ∉ P.val.asIdeal.map (algebraMap (𝓞 F) R) :=
    sourcePrimeUnit_pow_not_mem seed P.val P.property _
      (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) y hy 6
  have hxy : x * y ^ 6 ∉ P.val.asIdeal.map (algebraMap (𝓞 F) R) :=
    sourcePrimeUnit_mul_not_mem seed P.val P.property _
      (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) x (y ^ 6) hx hy6
  calc
    _ = sourcePrimeCharacterUnit F hζ S₀ P (x * y ^ 6) hxy :=
      sourcePrimeCharacterUnit_congr F hζ S₀ P _ hxy (sourceFrequencyCofactor_mul_sixth F hζ S₀ u hu r P)
    _ = sourcePrimeCharacterUnit F hζ S₀ P x hx * sourcePrimeCharacterUnit F hζ S₀ P (y ^ 6) hy6 :=
      sourceCharacterUnit_mul_actual seed P.val P.property _
        (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) _ x (y ^ 6) hx hy6 hxy
    _ = sourcePrimeCharacterUnit F hζ S₀ P x hx * sourcePrimeCharacterUnit F hζ S₀ P y hy ^ (6 : ℕ) := by
      exact congrArg (fun z : ℂˣ => sourcePrimeCharacterUnit F hζ S₀ P x hx * z)
        (sourceCharacterUnit_pow_actual seed P.val P.property _
          (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) _ y hy 6 hy6)
    _ = sourceResidualCharacterUnit F hζ S₀ u hu P := by
      rw [sourcePrimeCharacterUnit_pow_six F hζ S₀ P y hy, mul_one, sourceResidualCharacterUnit]

private theorem sourceCharacterUnit_one_actual (T : Finset (HeightOneSpectrum (𝓞 F)))
    (P : HeightOneSpectrum (𝓞 F)) (hP : P ∉ principalizingSet T)
    (a : PrincipalIntegerRing T)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T)) = Ideal.span {a})
    (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ)
    (h1 : (1 : PrincipalIntegerRing T) ∉ P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T))) :
    sourceCharacterUnit T P hP a ha χ 1 h1 = 1 := by
  apply Units.ext
  rw [sourceCharacterUnit_val]
  simp only [map_one, Units.val_one]

theorem sourceResidualCharacterUnit_one (P : SourceExteriorPrime F S₀) :
    sourceResidualCharacterUnit F hζ S₀ 1 one_ne_zero P = 1 := by
  have he := sourceFrequencyCofactor_base F hζ S₀ 1 one_ne_zero P
  rw [sourceElementExponents_one, Finsupp.zero_apply, pow_zero, one_mul] at he
  have h1 : (1 : R) ∉ P.val.asIdeal.map (algebraMap (𝓞 F) R) := fun hm =>
    (sourceFrequencyCofactor_spec F S₀ hζ 1 one_ne_zero 0 P).2 (he ▸ hm)
  calc
    _ = sourcePrimeCharacterUnit F hζ S₀ P 1 h1 :=
      sourcePrimeCharacterUnit_congr F hζ S₀ P _ h1 he.symm
    _ = 1 := sourceCharacterUnit_one_actual F seed P.val P.property _
      (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) _ h1

end
end ArtinMatthews.SourceEulerAssembly
