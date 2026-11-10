module

public import ArtinMatthews.SourceFrequencyUnitPart
public import ArtinMatthews.ReflectionCoefficientRow
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

/-! The actual sextic residue weights, including the absent-modulus
case, are invariant under multiplication by sixth powers of source units. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open VaryingKummerAnalytic AngularLambda
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

def sourceExteriorUnitToSourceUnits : exteriorUnitSubgroup (sourceHilbertSet F S₀) →* (sourceRing F S₀)ˣ where
  toFun u :=
    { val := sourceExteriorUnitToSourceRing F S₀ u
      inv := sourceExteriorUnitToSourceRing F S₀ u⁻¹
      val_inv := by rw [← map_mul, mul_inv_cancel, map_one]
      inv_val := by rw [← map_mul, inv_mul_cancel, map_one] }
  map_one' := by apply Units.ext; exact map_one (sourceExteriorUnitToSourceRing F S₀)
  map_mul' _ _ := by apply Units.ext; exact map_mul (sourceExteriorUnitToSourceRing F S₀) _ _

theorem sourceExteriorUnitToSourceUnits_val (u : exteriorUnitSubgroup (sourceHilbertSet F S₀)) :
    ((sourceExteriorUnitToSourceUnits F S₀ u : (sourceRing F S₀)ˣ) : sourceRing F S₀) =
      sourceExteriorUnitToSourceRing F S₀ u := rfl

theorem sourceLocalPowerWeight_mk_mul_sixth (P : HeightOneSpectrum (𝓞 F))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ) (hχ : χ ^ 6 = 1) (n : ℕ)
    (x : PrincipalIntegerRing S₀) (u : (PrincipalIntegerRing S₀)ˣ) :
    sourceLocalPowerWeight S₀ P hP a ha χ n
      (Ideal.Quotient.mk _ (x * (u : PrincipalIntegerRing S₀) ^ 6)) =
      sourceLocalPowerWeight S₀ P hP a ha χ n (Ideal.Quotient.mk _ x) := by
  by_cases hn : 0 < n
  · let e := (Ideal.quotEquivOfEq (generator_power_ideal S₀ P a ha n)).trans
      (generatorQuotientEquiv S₀ P hP a ha n)
    let ρ : PrincipalIntegerRing S₀ →+* ((𝓞 F) ⧸ P.asIdeal) :=
      (probeIdealResidueReduction F P n hn).comp (e.toRingHom.comp (Ideal.Quotient.mk (primePowerIdeal S₀ P n)))
    have h (y : PrincipalIntegerRing S₀) :
        sourceLocalPowerWeight S₀ P hP a ha χ n (Ideal.Quotient.mk _ y) = (χ ^ n) (ρ y) := by
      rw [sourceLocalPowerWeight, generatorPowerWeight_eq_transport, probePowerResidueWeight, dite_eq_left hn]
      rfl
    have hχn : (χ ^ n) ^ 6 = 1 := by rw [pow_right_comm, hχ, one_pow]
    have hu : ((χ ^ n) (ρ (u : PrincipalIntegerRing S₀))) ^ 6 = 1 := by
      rw [← MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), hχn,
        MulChar.one_apply (u.isUnit.map ρ)]
    rw [h, h, map_mul ρ, map_pow ρ, map_mul (χ ^ n), map_pow (χ ^ n), hu, mul_one]
  · have hn0 : n = 0 := by omega
    subst n
    rfl

variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourcePrimeExponentWeight_mul_sixth
    (χ : ∀ P : SourceExteriorPrime F S₀, MulChar ((𝓞 F) ⧸ P.val.asIdeal) ℂ)
    (hχ : ∀ P, χ P ^ 6 = 1) (e : SourcePrimeExponents F S₀)
    (x : sourceRing F S₀) (u : (sourceRing F S₀)ˣ) :
    sourcePrimeExponentWeight F hζ S₀ χ e (x * (u : sourceRing F S₀) ^ 6) =
      sourcePrimeExponentWeight F hζ S₀ χ e x := by
  unfold sourcePrimeExponentWeight Finsupp.prod
  apply Finset.prod_congr rfl
  intro P _
  exact sourceLocalPowerWeight_mk_mul_sixth F (sourceHilbertSeed F S₀) P.val P.property _
    (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) (χ P) (hχ P) (e P) x u

theorem reflectionPrimeCharacters_pow_six (P : SourceExteriorPrime F S₀) :
    reflectionPrimeCharacters F hζ S₀ P ^ 6 = 1 := by
  unfold reflectionPrimeCharacters
  rw [← cyclotomicAngularResidueCharacter_order hζ P.val
    (source_exterior_six_not_mem F S₀ P.val P.property)]
  exact pow_orderOf_eq_one _

theorem reflectionExponentResidueValue_mul_sixth (e : SourcePrimeExponents F S₀)
    (x : sourceRing F S₀) (u : (sourceRing F S₀)ˣ) :
    reflectionExponentResidueValue F hζ S₀ e (x * (u : sourceRing F S₀) ^ 6) =
      reflectionExponentResidueValue F hζ S₀ e x :=
  sourcePrimeExponentWeight_mul_sixth F S₀ hζ _ (reflectionPrimeCharacters_pow_six F S₀ hζ) e x u

end
end ArtinMatthews
