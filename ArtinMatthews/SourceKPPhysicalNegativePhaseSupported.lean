module

public import ArtinMatthews.SourceKPPhysicalNegativePhase
public import ArtinMatthews.SourceReflectionSupportedFrequency
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

/-! Apply the negative phase separation at the original supported
frequency index by restoring its exact integral numerator. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain VaryingKummerAnalytic
open AllowedGenerators SourceEulerAssembly SourcePhysical QuadraticWeil
open scoped NumberField Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "Pr" => SourceExteriorPrime K S₀
local notation "D" => sWholeDiagonal K S
local notation "gen" => sourcePrimeExponentUnit K hζ S₀
local notation "active" => sourceReflectionActiveExponents K S₀
variable {J : Ideal (𝓞 K)}

theorem sourceKPPhysicalNegativePhase_supported
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff K J ⊆ S)
    (u : exteriorUnitSubgroup (sourceHilbertSet K S₀))
    (f : Finset Pr) (d : E) (i : SourceReflectionSupportedTermIndex K S₀ f d)
    (εclass : ExteriorUnitSixthClasses S) (γ : sNormOneSixthSubgroup K S) :
    let b := gen (active f + d)
    let ν := (sourceReflectionSupportedFrequencyEquiv K S₀ hζ b f d (i,εclass,γ)).val.val
    let m := ν * b^2
    let εunit := sourceExteriorUnitSixthRepresentative S εclass
    sourceKPPhysicalNegativePhase K hζ S₀ hS η hJ u b (D m) =
      sourceKPPhysicalNegativeScalarPhase K hζ S₀ hS η hJ u εunit f i.val.1.val i.val.2.1 *
        sourceKPPhysicalNegativeRowPhase K hζ S₀ hS η hJ u d *
        sourceKPPhysicalNegativeColumnPhase K hζ S₀ hS η hJ u i.val.2.2.val := by
  let b := gen (active f + d)
  let ν := (sourceReflectionSupportedFrequencyEquiv K S₀ hζ b f d (i,εclass,γ)).val.val
  let εunit := sourceExteriorUnitSixthRepresentative S εclass
  let a := i.val.1.val
  let n := i.val.2.1
  let c := i.val.2.2.val
  have hν : D ν = γ.val.val * D (εunit.val * gen a * gen c * (gen n)^3 / b^2) :=
    sourceReflectionSupportedFrequencyEquiv_diagonal K S₀ hζ b f d i εclass γ
  have hnum : D (ν * b^2) = γ.val.val * D (εunit.val * gen (a + c + 3 • n)) := by
    rw [map_mul D, hν, mul_assoc, ← map_mul D, div_mul_cancel,
      sourceKPPhysicalNegativeNumerator_unit K hζ S₀ a c n]
    simp only [mul_assoc]
  change sourceKPPhysicalNegativePhase K hζ S₀ hS η hJ u b (D (ν * b^2)) = _
  rw [hnum]
  exact sourceKPPhysicalNegativePhase_split K hζ S₀ hS η hJ hcut u εunit f a n d c γ

end
end ArtinMatthews
