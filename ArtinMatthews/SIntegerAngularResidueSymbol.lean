module

public import ArtinMatthews.SIntegerPowerResidueSymbol
public import ArtinMatthews.ProbeAngularResidueSymbol
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
import GaloisCohomology.Kummer.Concrete.SUnitPreparation.PrimePowerKernelCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! The actual angular sextic character on an S-integer residue class
is the canonical power-residue symbol. The equality is proved by
injective reduction of sixth roots, with no reciprocity premise. -/
namespace ArtinMatthews.SIntegerResidueSymbol

open NumberField IsDedekindDomain KummerTheory
open AlgebraicNumberTheory.PowerResidueSymbols
open ArtinMatthews.SIntegerPrincipalization ArtinMatthews.SIntegerQuotient
open ArtinMatthews.VaryingKummerAnalytic ArtinMatthews.AngularLambda
open OAI OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] [Algebra BaseField K]

theorem angularRoot_eq_powerResidueOnUnit (P : HeightOneSpectrum (𝓞 K))
    (hsix : (6 : 𝓞 K) ∉ P.asIdeal) (hmu : (primitiveRoots 6 K).Nonempty)
    (u : ((𝓞 K) ⧸ P.asIdeal)ˣ) :
    probeIntegralSixthRoot K (probeAngularIntegralCharacter K P hsix u)
        (probeAngularIntegralCharacter_pow_six K P hsix u) =
      powerResidueOnUnit K P probeSix hmu (probePrimeNorm_coprime_six K P hsix) u := by
  apply rootsOfUnityReduction_injective K P probeSix (probePrimeNorm_coprime_six K P hsix)
  apply Subtype.ext
  apply Units.ext
  change Ideal.Quotient.mk P.asIdeal
      (algebraMap BaseIntegers (𝓞 K) (probeAngularIntegralCharacter K P hsix u)) =
    Ideal.Quotient.mk P.asIdeal
      (((powerResidueOnUnit K P probeSix hmu (probePrimeNorm_coprime_six K P hsix) u).1 :
        (𝓞 K)ˣ) : 𝓞 K)
  rw [probeAngularIntegralCharacter_reduce]
  exact (powerResidueOnUnit_reduce K P probeSix hmu (probePrimeNorm_coprime_six K P hsix) u).symm

theorem sIntegerAngularRoot_eq_symbol (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hsix : (6 : 𝓞 K) ∉ P.asIdeal) (hmu : (primitiveRoots 6 K).Nonempty)
    (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    probeIntegralSixthRoot K
        (probeAngularIntegralCharacter K P hsix (sIntegerResidueUnit K S₀ P hP a ha x hx))
        (probeAngularIntegralCharacter_pow_six K P hsix (sIntegerResidueUnit K S₀ P hP a ha x hx)) =
      sIntegerPowerResidueSymbol K S₀ P hP a ha probeSix hmu
        (probePrimeNorm_coprime_six K P hsix) x hx :=
  angularRoot_eq_powerResidueOnUnit K P hsix hmu _

end
end ArtinMatthews.SIntegerResidueSymbol
