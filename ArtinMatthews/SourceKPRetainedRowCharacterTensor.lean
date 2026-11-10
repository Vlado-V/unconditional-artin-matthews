module

public import ArtinMatthews.SourceKPRetainedFiniteClassTensor
public import ArtinMatthews.SourceReflectionLocalThetaCharacter
public import ArtinMatthews.SourceReflectionSUnitCharacter
public import ArtinMatthews.SourceReflectionSUnitCharacterContinuous
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

/-! The retained theta and row characters give the literal finite
unitary multiplier in the class tensor. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain QuadraticWeil VaryingKummerAnalytic
open SourcePhysical SourceEulerAssembly
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "U" => SWholeUnits K S
local notation "U₀" => SFiniteUnits K S

def sourceKPRetainedFiniteRowCharacter (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    {J : Ideal (𝓞 K)} (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) : U₀ →* ℂˣ := by
  let i : U₀ →* U := MonoidHom.inr (∀ w : InfinitePlace K, w.Completionˣ) U₀
  let θ : U₀ →* ℂˣ := sourceReflectionLocalThetaCharacter K S₀ hJ hζ hS η
  let r : U →* ℂˣ := sourceReflectionSUnitCharacter K hζ S₀ u
  exact θ * r.comp i

variable {J : Ideal (𝓞 K)}

theorem sourceKPRetainedFiniteRowCharacter_value
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (x : U) :
    sourceKPRetainedFiniteRowCharacter K hζ S₀ hS η hJ u x.2 =
      sourceReflectionLocalThetaCharacter K S₀ hJ hζ hS η x.2 *
        sourceReflectionSUnitCharacter K hζ S₀ u x := by
  let θ := sourceReflectionLocalThetaCharacter K S₀ hJ hζ hS η
  let r := sourceReflectionSUnitCharacter K hζ S₀ u
  change θ x.2 * r (1, x.2) = θ x.2 * r x
  exact congrArg (fun y : ℂˣ => θ x.2 * y)
    (sourceReflectionSUnitCharacter_eq_of_finite_eq K hζ S₀ u (x := (1, x.2)) (y := x) rfl)

theorem sourceKPRetainedFiniteRowCharacter_continuous
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) :
    Continuous (sourceKPRetainedFiniteRowCharacter K hζ S₀ hS η hJ u) := by
  let θ := sourceReflectionLocalThetaCharacter K S₀ hJ hζ hS η
  let r := sourceReflectionSUnitCharacter K hζ S₀ u
  change Continuous (fun z : U₀ => θ z * r (1, z))
  have hin : Continuous (fun z : U₀ => ((1, z) : U)) :=
    continuous_const.prodMk continuous_id
  exact (sourceReflectionLocalThetaCharacter_continuous K S₀ hJ hζ hS η).mul
    ((sourceReflectionSUnitCharacter_continuous K hζ S₀ u).comp hin)

theorem sourceKPRetainedFiniteRowCharacter_norm
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (z : U₀) :
    ‖(sourceKPRetainedFiniteRowCharacter K hζ S₀ hS η hJ u z : ℂ)‖ = 1 := by
  let θ := sourceReflectionLocalThetaCharacter K S₀ hJ hζ hS η
  let r := sourceReflectionSUnitCharacter K hζ S₀ u
  change ‖((θ z * r (1, z) : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_mul, norm_mul, sourceReflectionLocalThetaCharacter_norm K S₀ hJ hζ hS η z,
    sourceReflectionSUnitCharacter_norm K hζ S₀ u (1, z), mul_one]

theorem sourceKPRetainedFiniteRowCharacter_product
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (x : U) :
    ((sourceReflectionLocalThetaCharacter K S₀ hJ hζ hS η x.2 *
      sourceReflectionSUnitCharacter K hζ S₀ u x : ℂˣ) : ℂ) =
      ∏ P : S, (sourceKPRetainedFiniteCharacterAt K S
        (sourceKPRetainedFiniteRowCharacter K hζ S₀ hS η hJ u) P (x.2 P) : ℂ) := by
  rw [← sourceKPRetainedFiniteRowCharacter_value K hζ S₀ hS η hJ u x]
  exact sourceKPRetainedFiniteCharacter_product K S _ x.2

end
end ArtinMatthews
