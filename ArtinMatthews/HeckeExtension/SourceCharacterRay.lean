module

public import ArtinMatthews.HeckeExtension.SourceCharacterDescent
public import ArtinMatthews.AllowedIdealExtension
public import ArtinMatthews.ArtinRayIdealResidueRealization
public import ArtinMatthews.HeckeExtension.SourceSixthCongruence
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

/-! A genuine finite-order even ideal ray character extending a quadratic
character on the actual source B. The modulus depends only on K and S,
and its principal congruence kernel is proved by actual Hensel lifting. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain FractionalIdeal
open AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceComplementGlobalIdealCharacter
    (χ : chosenB K hζ S₀ →* ℂˣ) : FractionalIdealGroup K →* ℂˣ :=
  (sourceComplementIdealCharacter K hζ S₀ χ).comp (extendedIdealGroup K S₀)

theorem sourceComplementGlobalIdealCharacter_principal
    (χ : chosenB K hζ S₀ →* ℂˣ) (a : Kˣ) :
    sourceComplementGlobalIdealCharacter K hζ S₀ χ (toPrincipalIdeal (𝓞 K) K a) =
      sourceComplementFieldCharacter K hζ S₀ χ a := by
  change sourceComplementIdealCharacter K hζ S₀ χ
    (extendedIdealGroup K S₀ (toPrincipalIdeal (𝓞 K) K a)) = _
  rw [extendedIdealGroup_principal K S₀ a]
  exact sourceComplementIdealCharacter_principal K hζ S₀ χ a

theorem sourceComplementGlobalIdealCharacter_sq
    (χ : chosenB K hζ S₀ →* ℂˣ) (hχ : ∀ b, χ b ^ 2 = 1)
    (I : FractionalIdealGroup K) : sourceComplementGlobalIdealCharacter K hζ S₀ χ I ^ 2 = 1 :=
  sourceComplementIdealCharacter_sq K hζ S₀ χ hχ (extendedIdealGroup K S₀ I)

theorem sourceComplementGlobalIdealCharacter_principalValue
    (χ : chosenB K hζ S₀ →* ℂˣ) (a : 𝓞 K) (ha : a ≠ 0) :
    PrincipalRay.principalValue (sourceComplementGlobalIdealCharacter K hζ S₀ χ) a ha =
      sourceComplementFieldCharacter K hζ S₀ χ
        (Units.mk0 (a : K) (by exact_mod_cast ha)) := by
  have hi : integralIdealFractionalUnit (Ideal.span {a}) (by simpa using ha) =
      toPrincipalIdeal (𝓞 K) K (Units.mk0 (a : K) (by exact_mod_cast ha)) := by
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    exact FractionalIdeal.coeIdeal_span_singleton a
  exact (congrArg (sourceComplementGlobalIdealCharacter K hζ S₀ χ) hi).trans
    (sourceComplementGlobalIdealCharacter_principal K hζ S₀ χ _)

def sourceCharacterModulus : ℕ := by
  letI := source_isTotallyComplex K hζ
  exact (exists_sourceSixth_congruence_modulus K (sourceHilbertSet K S₀)).choose

theorem sourceCharacterModulus_spec : 0 < sourceCharacterModulus K hζ S₀ ∧
    ∀ (a : 𝓞 K) (ha : a ≠ 0),
      a - 1 ∈ rationalModulusIdeal (𝓞 K) (sourceCharacterModulus K hζ S₀) →
      sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀)
        (Units.mk0 (a : K) (by exact_mod_cast ha)) = 1 := by
  let := source_isTotallyComplex K hζ
  exact (exists_sourceSixth_congruence_modulus K (sourceHilbertSet K S₀)).choose_spec

theorem sourceCharacterModulusIdeal_ne_bot :
    rationalModulusIdeal (𝓞 K) (sourceCharacterModulus K hζ S₀) ≠ ⊥ := by
  let : NeZero (sourceCharacterModulus K hζ S₀) :=
    ⟨(sourceCharacterModulus_spec K hζ S₀).1.ne'⟩
  exact rationalModulusIdeal_ne_bot _

theorem sourceComplementGlobalIdealCharacter_congruence
    (χ : chosenB K hζ S₀ →* ℂˣ) :
    PrincipalIdealRay.KernelLaw (sourceComplementGlobalIdealCharacter K hζ S₀ χ)
      (rationalModulusIdeal (𝓞 K) (sourceCharacterModulus K hζ S₀)) := by
  intro a ha hc
  have he := sourceComplementGlobalIdealCharacter_principalValue K hζ S₀ χ a ha
  have hclass := (sourceCharacterModulus_spec K hζ S₀).2 a ha hc
  exact he.trans ((congrArg (sourceComplementCharacter K hζ S₀ χ) hclass).trans
    (sourceComplementCharacter K hζ S₀ χ).map_one)

def sourceComplementRayCharacter
    (χ : chosenB K hζ S₀ →* ℂˣ) (hχ : ∀ b, χ b ^ 2 = 1) :
    EvenIdealRayCharacter K (rationalModulusIdeal (𝓞 K) (sourceCharacterModulus K hζ S₀)) :=
  PrincipalIdealRay.realize (sourceComplementGlobalIdealCharacter K hζ S₀ χ) _
    (sourceCharacterModulusIdeal_ne_bot K hζ S₀)
    (sourceComplementGlobalIdealCharacter_congruence K hζ S₀ χ)
    ⟨2, by decide, sourceComplementGlobalIdealCharacter_sq K hζ S₀ χ hχ⟩

@[simp] theorem sourceComplementRayCharacter_idealHom
    (χ : chosenB K hζ S₀ →* ℂˣ) (hχ : ∀ b, χ b ^ 2 = 1) :
    (sourceComplementRayCharacter K hζ S₀ χ hχ).idealHom =
      sourceComplementGlobalIdealCharacter K hζ S₀ χ := rfl

theorem sourceComplementRayCharacter_allowed
    (χ : chosenB K hζ S₀ →* ℂˣ) (hχ : ∀ b, χ b ^ 2 = 1)
    (a : allowedSubgroup K hζ S₀) :
    (sourceComplementRayCharacter K hζ S₀ χ hχ).idealHom
        (toPrincipalIdeal (𝓞 K) K a.val) =
      χ ⟨sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) a.val, a.property⟩ := by
  exact (sourceComplementGlobalIdealCharacter_principal K hζ S₀ χ a.val).trans
    (sourceComplementCharacter_allowed K hζ S₀ χ ⟨_, a.property⟩)

end
end ArtinMatthews
