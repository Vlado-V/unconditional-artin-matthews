module

public import ArtinMatthews.SourceKPPositiveOrbitTwist
public import ArtinMatthews.SourceKPPhysicalRowWeight
public import ArtinMatthews.SourceSLocalQuotientSheet
public import ArtinMatthews.SourceThetaPositiveSheet
public import ArtinMatthews.SourceKPAllowedForwardOrbit
public import ArtinMatthews.SourceKPPositiveOrbitCharacter
public import ArtinMatthews.SourceKPPositivePhysicalOrbit
public import ArtinMatthews.SourceReflectionActiveBranchSupport
public import ArtinMatthews.SourceSLocalQuotientOrbitExpansion
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

namespace ArtinMatthews
open NumberField IsDedekindDomain QuadraticWeil VaryingKummerAnalytic
open SourcePhysical SourceReflection SourceEulerAssembly
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "Whole" => SWholeUnits K S
local notation "E" => SourcePrimeExponents K S₀
local notation "C" => ReflectionSquarefreeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "D" => sWholeDiagonal K S
local notation "gen" => sourcePrimeExponentUnit K hζ S₀
local notation "genR" => sourcePrimeExponentGenerator K hζ S₀
local notation "angle" => sourceKPOrientedHorizontal K hζ
local notation "bessel" => (fun _ : InfinitePlace K => 4*Real.pi)
local notation "rep" => sourceExteriorUnitSixthRepresentative S
local notation "Weight" => sourceKPPhysicalRowWeight K hζ S₀
local notation "Mask" => sourceKPPositivePhysicalActiveMask K S₀

attribute [local instance] positiveTwistLabelFintype
variable {J : Ideal (𝓞 K)}

def sourceKPPositivePhysicalBranchValue
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) (active : Finset PE) (x : Whole) : ℂ :=
  sourceKPPositivePhysicalFiniteValue K hζ S₀ e p.R p.M angle (one_le_two.trans hT.le)
    (sourceKPPositiveSeedData_q₀ K hζ S₀ p) (Mask e active) (Weight hS η hJ (rep u)) x

def sourceKPPositivePhysicalBranchAmplitude
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J)
    (e : E) (u : ExteriorUnitSixthClasses S) (active : Finset PE) (c : C) (n : E) : ℂ :=
  let A := c.val + 3 • n
  reflectionThetaValue K hζ S₀ hS η A *
    reflectionExponentResidueValue K hζ S₀ A (sourceExteriorUnitToSourceRing K S₀ (rep u)) *
    sourceReflectionPositiveTwistBranchFactor K hζ S₀ e active (genR A) *
    (reflectionGammaTwo K hζ S₀ c.val /
      ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) *
        (sourcePrimeExponentNorm K S₀ n : ℂ)))

theorem sourceKPPositivePhysicalBranchValue_hasSum
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff K J ⊆ S)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) (active : Finset PE) (x : Whole) :
    HasSum (fun z : (C × E) × Γ =>
      sourceKPPositivePhysicalBranchAmplitude K hζ S₀ hS η e u active z.1.1 z.1.2 *
      sourceThetaPositiveTensor K S bessel p.cutoff
        ((x * (z.2.val : Whole))*D (gen (z.1.1.val + 3 • z.1.2))))
      (sourceKPPositivePhysicalBranchValue K hζ S₀ hS η hJ hT p e u active x) := by
  let r := rep u
  let a (i : C × E) := sourceKPPositivePhysicalBranchAmplitude K hζ S₀ hS η e u active i.1 i.2
  have ha (c : C) (n : E) (γ : Γ) :
      let m := (sourceKPAllowedSquarefreeCubeFieldEquiv K hζ S₀ ((c,n),γ)).val
      (sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ r (D m) : ℂ) *
        sourceKPPositivePhysicalTwistScalar K hζ S₀ e (Mask e active) m *
        sourceKPRetainedExteriorWhittaker K hζ S₀ hS m = a (c,n) := by
    dsimp only
    rw [sourceKPPhysicalRowWholeCharacter_orbit K hζ S₀ hS η hJ hcut,
      sourceKPPositivePhysicalTwistScalar_branch_orbit K hζ S₀ hS e active c n γ,
      sourceKPAllowedSquarefreeCubeFieldEquiv_exteriorWhittaker K hζ S₀ hS c n γ]
    rfl
  exact sourceKPPositivePhysicalFiniteValue_orbit K hζ S₀ hS η hJ r hT p e (Mask e active) a ha x

theorem sourceKPPositivePhysicalBranchValue_invariant
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff K J ⊆ S)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) (active : Finset PE) :
    sourceSLocalSixthInvariant S (sourceKPPositivePhysicalBranchValue K hζ S₀ hS η hJ hT p e u active) :=
  sourceSLocalSixthInvariant_of_orbit_hasSum S _
    (fun z : C × E => fun x : Whole =>
      sourceKPPositivePhysicalBranchAmplitude K hζ S₀ hS η e u active z.1 z.2 *
      sourceThetaPositiveTensor K S bessel p.cutoff (x*D (gen (z.1.val + 3 • z.2))))
    (sourceKPPositivePhysicalBranchValue_hasSum K hζ S₀ hS η hJ hcut hT p e u active)

theorem sourceKPPositivePhysicalBranchValue_eq_zero
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff K J ⊆ S)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) (active : Finset PE)
    (ha : active ∈ e.support.powerset) (hbad : active ∉ sourceReflectionActiveChoices K S₀ e) (x : Whole) :
    sourceKPPositivePhysicalBranchValue K hζ S₀ hS η hJ hT p e u active x = 0 := by
  have h := sourceKPPositivePhysicalBranchValue_hasSum K hζ S₀ hS η hJ hcut hT p e u active x
  have he (c : C) (n : E) : sourceKPPositivePhysicalBranchAmplitude K hζ S₀ hS η e u active c n = 0 := by
    dsimp only [sourceKPPositivePhysicalBranchAmplitude]
    rw [sourceReflectionPositiveTwistBranchFactor_eq_zero_off_activeChoice K hζ S₀ e ha hbad,
      mul_zero,zero_mul]
  simpa only [he,zero_mul,tsum_zero] using h.tsum_eq.symm

end
end ArtinMatthews
