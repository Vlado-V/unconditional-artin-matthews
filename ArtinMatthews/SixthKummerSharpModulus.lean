module

public import ArtinMatthews.SixthExteriorReduction
public import ArtinMatthews.VaryingKummerAnalyticRayIdealModulus
public import ArtinMatthews.SixthLocalHensel
public import ArtinMatthews.ArtinFrobeniusConductorSupport
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


set_option backward.privateInPublic true
@[expose] public section

/-! The literal ideal m_S * rad_S(u), with fixed Hensel depths at S
and exponent one at every exterior prime in the radicand's support. -/
namespace ArtinMatthews
open IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section

variable {F : Type*} [Field F] [NumberField F]

def sixthWildPrimes (F : Type*) [Field F] [NumberField F] :
    Finset (HeightOneSpectrum (𝓞 F)) :=
  exteriorFractionalSupport (Ideal.span {(6 : 𝓞 F)} : FractionalIdeal (𝓞 F)⁰ F)

theorem mem_sixthWildPrimes (p : HeightOneSpectrum (𝓞 F)) :
    p ∈ sixthWildPrimes F ↔ (6 : 𝓞 F) ∈ p.asIdeal := by
  rw [sixthWildPrimes,mem_exteriorFractionalSupport]
  exact principal_count_ne_zero_iff_mem F 6 (by norm_num) p

def sixthKummerFixedIdeal (S : Finset (HeightOneSpectrum (𝓞 F))) : Ideal (𝓞 F) :=
  ∏ p ∈ S, p.asIdeal ^ sixthLocalHenselDepth p

def sixthExteriorRadicalPrimes (S : Finset (HeightOneSpectrum (𝓞 F))) (u : Fˣ) :
    Finset (HeightOneSpectrum (𝓞 F)) :=
  (exteriorFractionalSupport (toPrincipalIdeal (𝓞 F) F u)).filter (fun p => p ∉ S)

theorem mem_sixthExteriorRadicalPrimes (S : Finset (HeightOneSpectrum (𝓞 F)))
    (u : Fˣ) (p : HeightOneSpectrum (𝓞 F)) :
    p ∈ sixthExteriorRadicalPrimes S u ↔ p ∉ S ∧ exteriorPrincipalValuation p u ≠ 0 := by
  simp only [sixthExteriorRadicalPrimes,Finset.mem_filter,mem_exteriorFractionalSupport,
    exteriorPrincipalValuation,and_comm]

def sixthExteriorRadicalIdeal (S : Finset (HeightOneSpectrum (𝓞 F))) (u : Fˣ) :
    Ideal (𝓞 F) := ∏ p ∈ sixthExteriorRadicalPrimes S u, p.asIdeal

def sixthKummerSharpIdeal (S : Finset (HeightOneSpectrum (𝓞 F))) (u : Fˣ) :
    Ideal (𝓞 F) := sixthKummerFixedIdeal S * sixthExteriorRadicalIdeal S u

theorem sixthKummerFixedIdeal_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F))) :
    sixthKummerFixedIdeal S ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ p.ne_bot

theorem sixthExteriorRadicalIdeal_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F))) (u : Fˣ) :
    sixthExteriorRadicalIdeal S u ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => p.ne_bot

theorem sixthKummerSharpIdeal_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F))) (u : Fˣ) :
    sixthKummerSharpIdeal S u ≠ 0 :=
  mul_ne_zero (sixthKummerFixedIdeal_ne_zero S) (sixthExteriorRadicalIdeal_ne_zero S u)

theorem sixthKummerSharpIdeal_fixed_pow_dvd (S : Finset (HeightOneSpectrum (𝓞 F)))
    (u : Fˣ) (p : HeightOneSpectrum (𝓞 F)) (hp : p ∈ S) :
    p.asIdeal ^ sixthLocalHenselDepth p ∣ sixthKummerSharpIdeal S u :=
  (Finset.dvd_prod_of_mem (fun p : HeightOneSpectrum (𝓞 F) =>
    p.asIdeal ^ sixthLocalHenselDepth p) hp).trans (dvd_mul_right _ _)

theorem sixthKummerSharpIdeal_radical_dvd (S : Finset (HeightOneSpectrum (𝓞 F)))
    (u : Fˣ) (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∉ S) (hu : exteriorPrincipalValuation p u ≠ 0) :
    p.asIdeal ∣ sixthKummerSharpIdeal S u :=
  (Finset.dvd_prod_of_mem (fun p : HeightOneSpectrum (𝓞 F) => p.asIdeal)
    ((mem_sixthExteriorRadicalPrimes S u p).mpr ⟨hp,hu⟩)).trans (dvd_mul_left _ _)

theorem sixthKummerSharpIdeal_fixed_depth_le (S : Finset (HeightOneSpectrum (𝓞 F)))
    (u : Fˣ) (p : HeightOneSpectrum (𝓞 F)) (hp : p ∈ S) :
    sixthLocalHenselDepth p ≤ integralIdealFiniteModulus (sixthKummerSharpIdeal S u)
      (sixthKummerSharpIdeal_ne_zero S u) p := by
  exact (FiniteMultiplicity.of_prime_left p.prime (sixthKummerSharpIdeal_ne_zero S u)).le_multiplicity_of_pow_dvd
    (sixthKummerSharpIdeal_fixed_pow_dvd S u p hp)

theorem sixthKummerSharpIdeal_radical_depth_le (S : Finset (HeightOneSpectrum (𝓞 F)))
    (u : Fˣ) (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∉ S) (hu : exteriorPrincipalValuation p u ≠ 0) :
    1 ≤ integralIdealFiniteModulus (sixthKummerSharpIdeal S u)
      (sixthKummerSharpIdeal_ne_zero S u) p := by
  apply (FiniteMultiplicity.of_prime_left p.prime (sixthKummerSharpIdeal_ne_zero S u)).le_multiplicity_of_pow_dvd
  simpa only [pow_one] using sixthKummerSharpIdeal_radical_dvd S u p hp hu

theorem sixthKummerSharpIdeal_absNorm (S : Finset (HeightOneSpectrum (𝓞 F))) (u : Fˣ) :
    (sixthKummerSharpIdeal S u).absNorm=
      (sixthKummerFixedIdeal S).absNorm*(sixthExteriorRadicalIdeal S u).absNorm := map_mul _ _ _

theorem sixthKummerFixedIdeal_absNorm_pos (S : Finset (HeightOneSpectrum (𝓞 F))) :
    0 < (sixthKummerFixedIdeal S).absNorm :=
  Nat.pos_of_ne_zero fun h => sixthKummerFixedIdeal_ne_zero S (Ideal.absNorm_eq_zero_iff.mp h)

end
end ArtinMatthews
