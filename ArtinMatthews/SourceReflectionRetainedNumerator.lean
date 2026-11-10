module

public import ArtinMatthews.SourceReflectionSupportedFrequency
public import ArtinMatthews.SourceReflectionClassSelector
public import ArtinMatthews.SourceFrequencyPoissonArgument
public import ArtinMatthews.SourcePrimeExponentProducts
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

/-! The retained tensor sees the integral numerator. Its normalizing
unit and its sixth class are literal on the reflected frequency orbit. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain AllowedGenerators SourcePhysical
open scoped NumberField
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "S" => sourceHilbertSet F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "Prime" => SourceExteriorPrime F S₀
local notation "X" => ExteriorUnitSixthClasses (K := F) S
local notation "Γ" => sNormOneSixthSubgroup F S
local notation "D" => sWholeDiagonal F S
local notation "gen" => sourcePrimeExponentUnit F hζ S₀
local notation "cl" => sWholeGlobalClassMap F 6 S
local notation "C" => sourceReflectionExponentSixthClass F S₀ hζ
private def wholeSixthQuotient :
    SWholeUnits F (sourceHilbertSet F S₀) →* SWholePowerClasses F 6 (sourceHilbertSet F S₀) :=
  QuotientGroup.mk' (MonoidHom.range
    (powMonoidHom 6 : SWholeUnits F (sourceHilbertSet F S₀) →*
      SWholeUnits F (sourceHilbertSet F S₀)))

local notation "q₆" => wholeSixthQuotient F S₀

def sourceReflectionRetainedNumeratorUnit (a n c : E) (u : X) : Fˣ :=
  (sourceExteriorUnitSixthRepresentative S u).val * gen a * gen c * (gen n)^3

local notation "base" => sourceReflectionRetainedNumeratorUnit F S₀ hζ

theorem sourceReflectionRetainedNumeratorUnit_norm (a n c : E) (u : X) :
    sLocalNorm F S (D (base a n c u)) = sourceReflectionTermLength F S₀ a n c := by
  change fieldSNorm F S (base a n c u) = _
  have hu : fieldSNorm F S (sourceExteriorUnitSixthRepresentative S u).val = 1 :=
    fieldSNorm_sUnit F S (sourceExteriorUnitToActualSUnit F S
      (sourceExteriorUnitSixthRepresentative S u))
  simp only [sourceReflectionRetainedNumeratorUnit, map_mul, map_pow, hu, one_mul,
    sourcePrimeExponentUnit_fieldSNorm, sourceReflectionTermLength]

theorem sourceReflectionRetainedNumeratorUnit_class (a n c : E) (u : X) :
    cl (base a n c u) = sourceReflectionExteriorUnitClass F S₀ u * C a * C c * C n ^ 3 := by
  rw [sourceReflectionRetainedNumeratorUnit, map_mul, map_mul, map_mul, map_pow,
    ← sourceReflectionExteriorUnitClass_representative F S₀ u]
  rfl

private theorem normOneSixth_class_one (γ : Γ) : q₆ γ.val.val = 1 := by
  obtain ⟨t, ht⟩ := γ.property
  have hv : γ.val.val = D (t.val ^ 6) := by
    exact (congrArg Subtype.val ht).symm.trans (sNormOneSixthMap_val F S t)
  rw [hv, map_pow D, map_pow q₆]
  exact powerQuotient_pow_eq_one 6 _

private theorem supportedFrequency_class_base (b : Fˣ) (f : Finset Prime) (d : E)
    (i : SourceReflectionSupportedTermIndex F S₀ f d) (u : X) (γ : Γ) :
    cl ((sourceReflectionSupportedFrequencyEquiv F S₀ hζ b f d (i,u,γ)).val.val) =
      cl (base i.val.1.val i.val.2.1 i.val.2.2.val u / b^2) := by
  let ν := (sourceReflectionSupportedFrequencyEquiv F S₀ hζ b f d (i,u,γ)).val.val
  let m := base i.val.1.val i.val.2.1 i.val.2.2.val u / b^2
  have he : D ν = γ.val.val * D m :=
    sourceReflectionSupportedFrequencyEquiv_diagonal F S₀ hζ b f d i u γ
  calc
    cl ν = q₆ (D ν) := rfl
    _ = q₆ (γ.val.val * D m) := congrArg q₆ he
    _ = q₆ γ.val.val * q₆ (D m) := map_mul q₆ _ _
    _ = 1 * q₆ (D m) := congrArg (· * q₆ (D m)) (normOneSixth_class_one F S₀ γ)
    _ = cl m := one_mul (cl m)

theorem sourceReflectionSupportedFrequencyEquiv_retainedNumeratorClass (b : Fˣ)
    (f : Finset Prime) (d : E) (i : SourceReflectionSupportedTermIndex F S₀ f d) (u : X) (γ : Γ) :
    cl ((sourceReflectionSupportedFrequencyEquiv F S₀ hζ b f d (i,u,γ)).val.val * b^2) =
      sourceReflectionExteriorUnitClass F S₀ u * C i.val.1.val * C i.val.2.2.val * C i.val.2.1 ^ 3 := by
  let ν := (sourceReflectionSupportedFrequencyEquiv F S₀ hζ b f d (i,u,γ)).val.val
  let m := base i.val.1.val i.val.2.1 i.val.2.2.val u
  have he : cl ν = cl (m / b^2) := supportedFrequency_class_base F S₀ hζ b f d i u γ
  calc
    cl (ν * b^2) = cl ν * cl (b^2) := map_mul cl _ _
    _ = cl (m / b^2) * cl (b^2) := congrArg (· * cl (b^2)) he
    _ = cl ((m / b^2) * b^2) := (map_mul cl _ _).symm
    _ = cl m := congrArg cl (div_mul_cancel _ _)
    _ = _ := sourceReflectionRetainedNumeratorUnit_class F S₀ hζ _ _ _ u

theorem sourceReflectionSupportedFrequencyEquiv_reflectedClass (f : Finset Prime) (d : E)
    (i : SourceReflectionSupportedTermIndex F S₀ f d) (u : X) (γ : Γ) :
    cl ((sourceReflectionSupportedFrequencyEquiv F S₀ hζ
      (gen (sourceReflectionActiveExponents F S₀ f + d)) f d (i,u,γ)).val.val) =
      sourceReflectionProfileClass F S₀ hζ u f i.val.1.val i.val.2.1 (C d) (C i.val.2.2.val) := by
  let b := gen (sourceReflectionActiveExponents F S₀ f + d)
  let ν := (sourceReflectionSupportedFrequencyEquiv F S₀ hζ b f d (i,u,γ)).val.val
  have he : cl ν = cl (base i.val.1.val i.val.2.1 i.val.2.2.val u / b^2) :=
    supportedFrequency_class_base F S₀ hζ b f d i u γ
  refine he.trans ?_
  have hg : base i.val.1.val i.val.2.1 i.val.2.2.val u =
      (sourceExteriorUnitSixthRepresentative S u).val * gen (i.val.1.val + i.val.2.2.val + 3 • i.val.2.1) := by
    simp only [sourceReflectionRetainedNumeratorUnit, sourcePrimeExponentUnit_add]
    rw [show 3 • i.val.2.1 = i.val.2.1 + i.val.2.1 + i.val.2.1 by
      ext P
      simp only [Finsupp.nsmul_apply, nsmul_eq_mul, Finsupp.add_apply]
      omega,
      sourcePrimeExponentUnit_add, sourcePrimeExponentUnit_add, pow_three]
    ac_rfl
  rw [hg]
  simpa only [one_pow, one_mul] using sourceReflectionProfileClass_eq F S₀ hζ u f
    i.val.1.val i.val.2.1 d i.val.2.2.val 1

end
end ArtinMatthews.SourceEulerAssembly
