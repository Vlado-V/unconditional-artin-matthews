module

public import ArtinMatthews.AllowedIdealExtension
public import ArtinMatthews.HeckeExtension.ComplementCharacter
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The actual complement projection descends through the principal
S-integer ideal map. Its square-class reduction recovers the local
classes of the fixed allowed generators. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain FractionalIdeal ClassFieldTheory
open AllowedGenerators SIntegerPrincipalization
open scoped NumberField Classical nonZeroDivisors
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "B" => chosenB F hζ S₀


def sourceComplementClassProjection : SLocalRingPowerClasses F 6 S →* B :=
  @complementProjection (SLocalRingPowerClasses F 6 S) inferInstance
    (sLocalRingUnitImage F 6 S) (chosenB F hζ S₀) (chosenB_isCompl F hζ S₀)

@[simp] theorem sourceComplementClassProjection_allowed (b : B) :
    sourceComplementClassProjection F S₀ hζ b.val = b :=
  @complementProjection_right (SLocalRingPowerClasses F 6 S) inferInstance
    (sLocalRingUnitImage F 6 S) (chosenB F hζ S₀) (chosenB_isCompl F hζ S₀) b


theorem sourceComplementClassProjection_unit (u : SUnitGroup (K := F) S) :
    sourceComplementClassProjection F S₀ hζ (sLocalRingGlobalClassMap F 6 S u.val) = 1 :=
  @complementProjection_left (SLocalRingPowerClasses F 6 S) inferInstance
    (sLocalRingUnitImage F 6 S) (chosenB F hζ S₀) (chosenB_isCompl F hζ S₀)
    ⟨_, ⟨u, rfl⟩⟩

def sourceComplementFieldClass : Fˣ →* B :=
  (sourceComplementClassProjection F S₀ hζ).comp (sLocalRingGlobalClassMap F 6 S)

theorem sourceComplementFieldClass_principal_kernel :
    (toPrincipalIdeal (sourceRing F S₀) F).ker ≤
      (sourceComplementFieldClass F S₀ hζ).ker := by
  intro a ha
  apply MonoidHom.mem_ker.mpr
  have hu := (principal_eq_one_iff_sUnit F S₀ a).mp (MonoidHom.mem_ker.mp ha)
  exact sourceComplementClassProjection_unit F S₀ hζ ⟨a, hu⟩


def sourceComplementIdealClass : idealGroup F S₀ →* B :=
  (toPrincipalIdeal (sourceRing F S₀) F).liftOfSurjective
    (exists_fractional_field_generator (sourceHilbertSeed F S₀))
    ⟨sourceComplementFieldClass F S₀ hζ,
      sourceComplementFieldClass_principal_kernel F S₀ hζ⟩

@[simp] theorem sourceComplementIdealClass_principal (a : Fˣ) :
    sourceComplementIdealClass F S₀ hζ (toPrincipalIdeal (sourceRing F S₀) F a) =
      sourceComplementFieldClass F S₀ hζ a :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a

def sourceComplementGlobalIdealClass : FractionalIdealGroup F →* B :=
  (sourceComplementIdealClass F S₀ hζ).comp (extendedIdealGroup F S₀)

@[simp] theorem sourceComplementGlobalIdealClass_principal (a : Fˣ) :
    sourceComplementGlobalIdealClass F S₀ hζ (toPrincipalIdeal (𝓞 F) F a) =
      sourceComplementFieldClass F S₀ hζ a := by
  change sourceComplementIdealClass F S₀ hζ
    (extendedIdealGroup F S₀ (toPrincipalIdeal (𝓞 F) F a)) = _
  rw [extendedIdealGroup_principal, sourceComplementIdealClass_principal]


def localSixthToSquare (L : Type*) [Field L] : PowerClassGroup L 6 →* PowerClassGroup L 2 :=
  QuotientGroup.map (powMonoidHom 6 : Lˣ →* Lˣ).range
    (powMonoidHom 2 : Lˣ →* Lˣ).range (MonoidHom.id _) (by
      rintro _ ⟨u, rfl⟩
      exact ⟨u ^ 3, by simp only [powMonoidHom_apply, ← pow_mul]; rfl⟩)

@[simp] theorem localSixthToSquare_powerClass (L : Type*) [Field L] (u : Lˣ) :
    localSixthToSquare L (powerClass L 6 u) = powerClass L 2 u := rfl


def sLocalSixthToSquare : SLocalPowerClasses F 6 S →* SLocalPowerClasses F 2 S where
  toFun x v := localSixthToSquare (v.val.adicCompletion F) (x v)
  map_one' := by funext v; exact map_one _
  map_mul' x y := by funext v; exact map_mul _ _ _

@[simp] theorem sLocalSixthToSquare_globalClass (a : Fˣ) :
    sLocalSixthToSquare F S₀ (sLocalGlobalClassMap F 6 S a) =
      sLocalGlobalClassMap F 2 S a := rfl


def sourceComplementSquareClass : B →* SLocalPowerClasses F 2 S := by
  letI := source_isTotallyComplex F hζ
  exact (sLocalSixthToSquare F S₀).comp
    (((sLocalRingPowerEquiv F 6 S).trans (sWholePowerEquiv F 6 S)).toMonoidHom.comp
      (chosenB F hζ S₀).subtype)


@[simp] theorem sourceComplementSquareClass_allowed (a : allowedSubgroup F hζ S₀) :
    sourceComplementSquareClass F S₀ hζ
      ⟨sLocalRingGlobalClassMap F 6 S a.val, a.property⟩ =
      sLocalGlobalClassMap F 2 S a.val := by
  let := source_isTotallyComplex F hζ
  change sLocalSixthToSquare F S₀
    (sWholePowerEquiv F 6 S (sLocalRingPowerEquiv F 6 S
      (sLocalRingGlobalClassMap F 6 S a.val))) = _
  rw [sLocalRingPowerEquiv_globalClass, sWholePowerEquiv_globalClass]
  rfl


def sourceQuadraticIdealClass : FractionalIdealGroup F →* SLocalPowerClasses F 2 S :=
  (sourceComplementSquareClass F S₀ hζ).comp (sourceComplementGlobalIdealClass F S₀ hζ)


theorem sourceQuadraticIdealClass_allowed (a : allowedSubgroup F hζ S₀) :
    sourceQuadraticIdealClass F S₀ hζ (toPrincipalIdeal (𝓞 F) F a.val) =
      sLocalGlobalClassMap F 2 S a.val := by
  change sourceComplementSquareClass F S₀ hζ
    (sourceComplementGlobalIdealClass F S₀ hζ (toPrincipalIdeal (𝓞 F) F a.val)) = _
  rw [sourceComplementGlobalIdealClass_principal]
  change sourceComplementSquareClass F S₀ hζ
    (sourceComplementClassProjection F S₀ hζ
      (sLocalRingGlobalClassMap F 6 S a.val)) = _
  rw [sourceComplementClassProjection_allowed F S₀ hζ
    ⟨sLocalRingGlobalClassMap F 6 S a.val, a.property⟩]
  exact sourceComplementSquareClass_allowed F S₀ hζ a

end
end ArtinMatthews.SourceEulerAssembly
