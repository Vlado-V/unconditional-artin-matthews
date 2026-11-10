module

public import ArtinMatthews.SourceReflectionSUnitPhase
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

/-! The oriented row S-unit phase as a character on the actual whole S-local units. -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain KummerTheory ClassFieldTheory
open AllowedGenerators SIntegerAllowedReciprocity VaryingKummerAnalytic AngularLambda
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S" => sourceHilbertSet K S₀
local notation "X" => exteriorUnitSubgroup S
local notation "U" => SWholeUnits K S
local notation "Q" => SLocalRingPowerClasses K 6 S
local notation "classOf" => sLocalRingGlobalClassMap K 6 S
local notation "classMap" => MulEquiv.toMonoidHom (MulEquiv.symm (sLocalRingPowerEquiv K 6 S))
local notation "quotientMap" => QuotientGroup.mk' (MonoidHom.range (powMonoidHom ((6 : ℕ+) : ℕ) : U →* U))

def sourceReflectionSUnitClassCharacter (u : X) : Q →* ℂˣ :=
  (Units.map (sourceComplexEmbedding hζ).toMonoidHom).comp
    ((nthRootsSubgroup K 6).subtype.comp
      (invMonoidHom.comp ((nthRootsSubgroupEquivRootsOfUnity K 6).symm.toMonoidHom.comp
        ((paperSourceHilbertForm K hζ S).flip (classOf u.val)))))

theorem sourceReflectionSUnitClassCharacter_val (u : X) (a : Q) :
    (sourceReflectionSUnitClassCharacter K hζ S₀ u a : ℂ) =
      sourceReflectionSUnitClassPhase K hζ S₀ u a := rfl

def sourceReflectionSUnitCharacter (u : X) : U →* ℂˣ :=
  (sourceReflectionSUnitClassCharacter K hζ S₀ u).comp ((classMap).comp quotientMap)

theorem sourceReflectionSUnitCharacter_val (u : X) (x : U) :
    (sourceReflectionSUnitCharacter K hζ S₀ u x : ℂ) =
      sourceReflectionSUnitClassPhase K hζ S₀ u (classMap (quotientMap x)) := rfl

theorem sourceReflectionSUnitCharacter_norm (u : X) (x : U) :
    ‖(sourceReflectionSUnitCharacter K hζ S₀ u x : ℂ)‖ = 1 := by
  rw [sourceReflectionSUnitCharacter_val]
  exact sourceReflectionSUnitClassPhase_norm K hζ S₀ u _

theorem sourceReflectionSUnitCharacter_diagonal (u : X) (a : Kˣ) :
    (sourceReflectionSUnitCharacter K hζ S₀ u (sWholeDiagonal K S a) : ℂ) =
      sourceReflectionSUnitClassPhase K hζ S₀ u (classOf a) := by
  rw [sourceReflectionSUnitCharacter_val]
  apply congrArg (sourceReflectionSUnitClassPhase K hζ S₀ u)
  change (sLocalRingPowerEquiv K 6 S).symm (sWholeGlobalClassMap K 6 S a) = classOf a
  rw [← sLocalRingPowerEquiv_globalClass, MulEquiv.symm_apply_apply]

theorem sourceReflectionSUnitCharacter_primeExponent (u : X) (a : SourcePrimeExponents K S₀) :
    (sourceReflectionSUnitCharacter K hζ S₀ u
        (sWholeDiagonal K S (sourcePrimeExponentUnit K hζ S₀ a)) : ℂ) =
      reflectionExponentResidueValue K hζ S₀ a (sourceExteriorUnitToSourceRing K S₀ u) := by
  rw [sourceReflectionSUnitCharacter_diagonal, sourceReflectionExponentResidueValue_sUnit_eq_classPhase]

theorem sourceReflectionSUnitCharacter_sixth (u : X) (x : U) :
    sourceReflectionSUnitCharacter K hζ S₀ u (x^6) = 1 := by
  have hq : quotientMap (x^6) = 1 :=
    (QuotientGroup.eq_one_iff (x^6)).mpr ⟨x, rfl⟩
  change sourceReflectionSUnitClassCharacter K hζ S₀ u (classMap (quotientMap (x^6))) = 1
  rw [hq, map_one, map_one]

theorem sourceReflectionSUnitCharacter_pow_six_eq_one (u : X) (x : U) :
    (sourceReflectionSUnitCharacter K hζ S₀ u x)^6 = 1 := by
  rw [← map_pow, sourceReflectionSUnitCharacter_sixth]

theorem sourceReflectionSUnitCharacter_eq_of_finitePowerClass_eq (u : X) {x y : U}
    (h : ∀ v : S, powerClass (v.1.adicCompletion K) 6 (x.2 v) =
      powerClass (v.1.adicCompletion K) 6 (y.2 v)) :
    sourceReflectionSUnitCharacter K hζ S₀ u x = sourceReflectionSUnitCharacter K hζ S₀ u y := by
  let : NumberField.IsTotallyComplex K := source_isTotallyComplex K hζ
  have he : quotientMap x = quotientMap y := (sWholePowerEquiv K 6 S).injective (by
    rw [sWholePowerEquiv_mk, sWholePowerEquiv_mk]
    exact funext h)
  exact congrArg (sourceReflectionSUnitClassCharacter K hζ S₀ u ∘ classMap) he

theorem sourceReflectionSUnitCharacter_eq_of_finite_eq (u : X) {x y : U} (h : x.2 = y.2) :
    sourceReflectionSUnitCharacter K hζ S₀ u x = sourceReflectionSUnitCharacter K hζ S₀ u y :=
  sourceReflectionSUnitCharacter_eq_of_finitePowerClass_eq K hζ S₀ u (fun v => congrArg (powerClass (v.1.adicCompletion K) 6) (congrFun h v))

theorem sourceReflectionSUnitCharacter_arch (u : X) (x : ∀ w : InfinitePlace K, w.Completionˣ) :
    sourceReflectionSUnitCharacter K hζ S₀ u (x,1) = 1 :=
  (sourceReflectionSUnitCharacter_eq_of_finite_eq K hζ S₀ u (x := (x,1)) (y := 1) rfl).trans (map_one _)

theorem sourceReflectionSUnitCharacter_eq_of_finite_sixth_mul (u : X) {x y : U}
    (z : ∀ v : S, (v.1.adicCompletion K)ˣ) (h : x.2 = y.2 * z^6) :
    sourceReflectionSUnitCharacter K hζ S₀ u x = sourceReflectionSUnitCharacter K hζ S₀ u y := by
  calc
    _ = sourceReflectionSUnitCharacter K hζ S₀ u (y * ((1,z) : U)^6) :=
      sourceReflectionSUnitCharacter_eq_of_finite_eq K hζ S₀ u h
    _ = _ := by rw [map_mul, sourceReflectionSUnitCharacter_sixth, mul_one]

end
end ArtinMatthews.SourceEulerAssembly
