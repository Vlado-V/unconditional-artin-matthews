module

public import ArtinMatthews.SLocalNormOneGroup
public import ArtinMatthews.SourceKPPhysicalHorizontal
public import ArtinMatthews.SourceKPPhysicalRowCharacter
public import ArtinMatthews.SourceKPPositiveOrbitCharacter
public import ArtinMatthews.SourceKPReflectionPhaseOrientation
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

/-! Separate the actual negative Fourier phase into a fixed scalar, one
row factor, and one column factor. The argument of the whole character
is the integral numerator of the signed frequency. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain VaryingKummerAnalytic
open AllowedGenerators SourceEulerAssembly SourcePhysical QuadraticWeil
open scoped NumberField Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "U" => SWholeUnits K S
local notation "E" => SourcePrimeExponents K S₀
local notation "Pr" => SourceExteriorPrime K S₀
local notation "V" => InfinitePlace K
local notation "D" => sWholeDiagonal K S
local notation "gen" => sourcePrimeExponentUnit K hζ S₀
local notation "active" => sourceReflectionActiveExponents K S₀
local notation "eps" => sourceKPOrientedHorizontal K hζ
local notation "places" => sourceKPAllInfinitePlaces K

theorem sourceKPPhysicalNegativeNumerator_unit (a c n : E) :
    gen (a + c + 3 • n) = gen a * gen c * (gen n)^3 := by
  have hn : 3 • n = n + n + n := by
    ext P
    simp only [Finsupp.nsmul_apply, nsmul_eq_mul, Finsupp.add_apply]
    omega
  have h3 : gen (3 • n) = (gen n)^3 := by
    rw [hn, sourcePrimeExponentUnit_add, sourcePrimeExponentUnit_add, pow_three, mul_assoc]
  rw [sourcePrimeExponentUnit_add, sourcePrimeExponentUnit_add K hζ S₀ a c, h3]

variable {J : Ideal (𝓞 K)}

def sourceKPPhysicalNegativePhase
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (b : Kˣ) (m : U) : ℂ :=
  let χ := sourceKPPhysicalRowFiniteCharacter K hζ S₀ hS η hJ u
  let X := sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ u
  ((χ (sourceKPSLocalReflectionArgument K S b))⁻¹ : ℂˣ).val *
    ((X m)⁻¹ : ℂˣ).val * sourceKPReflectionProductPhase K hζ b eps places

def sourceKPPhysicalNegativeScalarPhase
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u εunit : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (f : Finset Pr) (a n : E) : ℂ :=
  let X := sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ u
  (-1 : ℂ)^Fintype.card V *
    ((X (D (εunit.val * gen a * (gen n)^3)))⁻¹ : ℂˣ).val *
    (X (D (gen (active f))) : ℂ)^2

def sourceKPPhysicalNegativeRowPhase
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (d : E) : ℂ :=
  (sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ u (D (gen d)) : ℂ)^2

def sourceKPPhysicalNegativeColumnPhase
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (c : E) : ℂ :=
  ((sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ u (D (gen c)))⁻¹ : ℂˣ).val

theorem sourceKPPhysicalNegativeScalarPhase_norm
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u εunit : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (f : Finset Pr) (a n : E) :
    ‖sourceKPPhysicalNegativeScalarPhase K hζ S₀ hS η hJ u εunit f a n‖ = 1 := by
  simp only [sourceKPPhysicalNegativeScalarPhase, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    Units.val_inv_eq_inv_val, norm_inv, sourceKPPhysicalRowWholeCharacter_norm, inv_one, mul_one]

theorem sourceKPPhysicalNegativeRowPhase_norm
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (d : E) :
    ‖sourceKPPhysicalNegativeRowPhase K hζ S₀ hS η hJ u d‖ = 1 := by
  simp only [sourceKPPhysicalNegativeRowPhase, norm_pow, sourceKPPhysicalRowWholeCharacter_norm, one_pow]

theorem sourceKPPhysicalNegativeColumnPhase_norm
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (c : E) :
    ‖sourceKPPhysicalNegativeColumnPhase K hζ S₀ hS η hJ u c‖ = 1 := by
  simp only [sourceKPPhysicalNegativeColumnPhase, Units.val_inv_eq_inv_val, norm_inv,
    sourceKPPhysicalRowWholeCharacter_norm, inv_one]

theorem sourceKPPhysicalNegativePhase_split
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff K J ⊆ S)
    (u εunit : exteriorUnitSubgroup (sourceHilbertSet K S₀))
    (f : Finset Pr) (a n d c : E) (γ : sNormOneSixthSubgroup K S) :
    let b := gen (active f + d)
    let m := γ.val.val * D (εunit.val * gen (a + c + 3 • n))
    sourceKPPhysicalNegativePhase K hζ S₀ hS η hJ u b m =
      sourceKPPhysicalNegativeScalarPhase K hζ S₀ hS η hJ u εunit f a n *
        sourceKPPhysicalNegativeRowPhase K hζ S₀ hS η hJ u d *
        sourceKPPhysicalNegativeColumnPhase K hζ S₀ hS η hJ u c := by
  let b := gen (active f + d)
  let m := γ.val.val * D (εunit.val * gen (a + c + 3 • n))
  let χ := sourceKPPhysicalRowFiniteCharacter K hζ S₀ hS η hJ u
  let X := sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ u
  let ρ := sourceKPReflectionProductPhase K hζ b eps places
  let q := εunit.val * gen a * (gen n)^3
  have hnum : εunit.val * gen (a + c + 3 • n) = q * gen c := by
    rw [sourceKPPhysicalNegativeNumerator_unit K hζ S₀ a c n]
    dsimp only [q]
    simp only [mul_assoc]
    rw [mul_comm (gen c) ((gen n)^3)]
  have hB : X (D b) = X (D (gen (active f))) * X (D (gen d)) := by
    change X (D (gen (active f + d))) = _
    rw [sourcePrimeExponentUnit_add, map_mul D, map_mul X]
  have hM : X m = X (D q) * X (D (gen c)) := by
    change X (γ.val.val * D (εunit.val * gen (a + c + 3 • n))) = _
    have hγ : X γ.val.val = 1 :=
      sourceKPPhysicalRowWholeCharacter_gamma K hζ S₀ hS η hJ hcut u γ
    rw [map_mul X, hγ, one_mul, hnum, map_mul D, map_mul X]
  change (((χ (sourceKPSLocalReflectionArgument K S b))⁻¹ : ℂˣ).val *
    ((X m)⁻¹ : ℂˣ).val) * ρ = _
  calc
    _ = (((χ (sourceKPSLocalReflectionArgument K S b))⁻¹ : ℂˣ).val * ρ) *
        ((X m)⁻¹ : ℂˣ).val := mul_right_comm _ _ _
    _ = (-1 : ℂ)^Fintype.card V * (X (D b) : ℂ)^2 * ((X m)⁻¹ : ℂˣ).val := by
      rw [sourceKPReflectedFiniteArchPhase_eq_whole K hζ S₀ hS η hJ u b]
    _ = _ := by
      rw [hB, Units.val_mul, mul_pow, hM, mul_inv_rev, Units.val_mul]
      change (-1 : ℂ)^Fintype.card V *
        ((X (D (gen (active f))) : ℂ)^2 * (X (D (gen d)) : ℂ)^2) *
        (((X (D (gen c)))⁻¹ : ℂˣ).val * ((X (D q))⁻¹ : ℂˣ).val) =
        ((-1 : ℂ)^Fintype.card V * ((X (D q))⁻¹ : ℂˣ).val *
          (X (D (gen (active f))) : ℂ)^2) * (X (D (gen d)) : ℂ)^2 *
            ((X (D (gen c)))⁻¹ : ℂˣ).val
      ring

end
end ArtinMatthews
