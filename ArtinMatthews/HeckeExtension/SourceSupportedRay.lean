module

public import ArtinMatthews.HeckeExtension.SourceCharacterRay
public import ArtinMatthews.SixthKummerSharpModulus
public import ArtinMatthews.VaryingKummerAnalyticRayCompletedCongruence
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
public import Mathlib.RingTheory.RegularLocalRing.Defs
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

/-! Sharpen the fixed ray modulus to its literal S-supported ideal.
The earlier rational modulus remains a valid independently checked bound. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain FractionalIdeal
open AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical nonZeroDivisors BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem sixthKummerFixedIdeal_support
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (integralIdealFiniteModulus (sixthKummerFixedIdeal S)
      (sixthKummerFixedIdeal_ne_zero S)).support = S := by
  ext p
  rw [integralIdealFiniteModulus_mem_support]
  constructor
  · intro hp
    obtain ⟨q, hq, hd⟩ := (p.prime.dvd_finsetProd_iff
      (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal ^ sixthLocalHenselDepth q)).mp hp
    have hqp : q.asIdeal ≤ p.asIdeal := Ideal.le_of_dvd (p.prime.dvd_of_dvd_pow hd)
    have he : q = p := HeightOneSpectrum.ext
      (q.isMaximal.eq_of_le p.isPrime.ne_top hqp)
    exact he ▸ hq
  · intro hp
    exact (dvd_pow_self _ (sixthLocalHenselDepth_pos p).ne').trans
      (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (𝓞 K) =>
        q.asIdeal ^ sixthLocalHenselDepth q) hp)

theorem sixthKummerFixedIdeal_completed_congruence
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : 𝓞 K)
    (ha : a - 1 ∈ sixthKummerFixedIdeal S) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
    algebraMap (𝓞 K) (v.adicCompletionIntegers K) a - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ sixthLocalHenselDepth v := by
  have hd : v.asIdeal ^ sixthLocalHenselDepth v ∣ sixthKummerFixedIdeal S :=
    Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (𝓞 K) =>
      q.asIdeal ^ sixthLocalHenselDepth q) hv
  have hp : a - 1 ∈ v.asIdeal ^ sixthLocalHenselDepth v := Ideal.le_of_dvd hd ha
  have hc := (completed_integral_mem_prime_pow_iff v _ (a - 1)).mpr hp
  simpa only [map_sub, map_one] using hc

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

theorem sourceComplementGlobalIdealCharacter_supported_congruence
    (χ : chosenB K hζ S₀ →* ℂˣ) :
    PrincipalIdealRay.KernelLaw (sourceComplementGlobalIdealCharacter K hζ S₀ χ)
      (sixthKummerFixedIdeal (sourceHilbertSet K S₀)) := by
  intro a ha hc
  let := source_isTotallyComplex K hζ
  have hf := sLocalGlobalSixthClass_eq_one_of_higher_congruence K
    (sourceHilbertSet K S₀) a ha (fun v hv =>
      sixthKummerFixedIdeal_completed_congruence K (sourceHilbertSet K S₀) a hc v hv)
  have hclass := sLocalRingGlobalClass_eq_one_of_finite K 6 (sourceHilbertSet K S₀)
    (Units.mk0 (a : K) (by exact_mod_cast ha)) hf
  exact (sourceComplementGlobalIdealCharacter_principalValue K hζ S₀ χ a ha).trans
    ((congrArg (sourceComplementCharacter K hζ S₀ χ) hclass).trans
      (sourceComplementCharacter K hζ S₀ χ).map_one)

def sourceSupportedRayCharacter
    (χ : chosenB K hζ S₀ →* ℂˣ) (hχ : ∀ b, χ b ^ 2 = 1) :
    EvenIdealRayCharacter K (sixthKummerFixedIdeal (sourceHilbertSet K S₀)) :=
  PrincipalIdealRay.realize (sourceComplementGlobalIdealCharacter K hζ S₀ χ) _
    (sixthKummerFixedIdeal_ne_zero _)
    (sourceComplementGlobalIdealCharacter_supported_congruence K hζ S₀ χ)
    ⟨2, by decide, sourceComplementGlobalIdealCharacter_sq K hζ S₀ χ hχ⟩

@[simp] theorem sourceSupportedRayCharacter_idealHom
    (χ : chosenB K hζ S₀ →* ℂˣ) (hχ : ∀ b, χ b ^ 2 = 1) :
    (sourceSupportedRayCharacter K hζ S₀ χ hχ).idealHom =
      sourceComplementGlobalIdealCharacter K hζ S₀ χ := rfl

theorem sourceSupportedRayCharacter_allowed
    (χ : chosenB K hζ S₀ →* ℂˣ) (hχ : ∀ b, χ b ^ 2 = 1)
    (a : allowedSubgroup K hζ S₀) :
    (sourceSupportedRayCharacter K hζ S₀ χ hχ).idealHom
        (toPrincipalIdeal (𝓞 K) K a.val) =
      χ ⟨sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) a.val, a.property⟩ := by
  exact (sourceComplementGlobalIdealCharacter_principal K hζ S₀ χ a.val).trans
    (sourceComplementCharacter_allowed K hζ S₀ χ ⟨_, a.property⟩)

end
end ArtinMatthews
