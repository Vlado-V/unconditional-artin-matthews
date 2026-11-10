module

public import ArtinMatthews.SourceKPRetainedNegativeClass
public import ArtinMatthews.SourceKPReflectedNumerator
public import ArtinMatthews.SourceKPPhysicalNegativePhase
public import ArtinMatthews.SourceReflectionExteriorGuards
public import ArtinMatthews.SourceKPPhysicalNegativePhaseSupported
public import ArtinMatthews.SourceReflectionPhysicalCoefficientBound
public import ArtinMatthews.SourceReflectionRetainedNumerator
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

/-! The normalized numerator and denominator classes give the exact
finite slices of the retained phase. The arithmetic coefficient uses
the original signed exterior factors and their Dirichlet bound. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain QuadraticWeil VaryingKummerAnalytic
open SourcePhysical SourceEulerAssembly
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "X" => ExteriorUnitSixthClasses S
local notation "Q" => SWholePowerClasses K 6 S
local notation "L" => SLocalPowerClasses K 6 S
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "D" => sWholeDiagonal K S
local notation "gen" => sourcePrimeExponentUnit K hζ S₀
local notation "C" => sourceReflectionExponentSixthClass K S₀ hζ
local notation "cl" => sWholeGlobalClassMap K 6 S
local notation "rep" => sourceExteriorUnitSixthRepresentative S
local notation "b[" f "," d "]" => gen (sourceReflectionActiveExponents K S₀ f+d)

def sourceKPReflectedClassWeight (f : Finset PE) (a n : E) (ε : X)
    (sd sc : Q) (r : L) : ℂ :=
  sourceKPRetainedNegativeClass K hζ S₀
    (sourceReflectionDenominatorSixthClass K S₀ hζ f sd)
    (sourceReflectionExteriorUnitClass K S₀ ε * C a * sc * C n ^ 3) r

theorem sourceKPReflectedClassWeight_norm_le (f : Finset PE) (a n : E) (ε : X)
    (sd sc : Q) (r : L) :
    ‖sourceKPReflectedClassWeight K hζ S₀ f a n ε sd sc r‖ ≤ 1 :=
  sourceKPRetainedNegativeClass_norm_le K hζ S₀ _ _ _

theorem sourceKPReflectedClassWeight_supported (f : Finset PE) (d : E)
    (i : SourceReflectionSupportedTermIndex K S₀ f d) (ε : X) (γ : Γ) (r : L) :
    sourceKPReflectedClassWeight K hζ S₀ f i.val.1.val i.val.2.1 ε (C d) (C i.val.2.2.val) r =
      sourceKPRetainedNegativeClass K hζ S₀ (cl (((b[f,d])⁻¹)^2))
        (cl (sourceKPReflectedNumerator K hζ S₀ f d i ε γ)) r := by
  unfold sourceKPReflectedClassWeight
  rw [sourceReflectionDenominatorSixthClass_eq]
  have hm := sourceReflectionSupportedFrequencyEquiv_retainedNumeratorClass K S₀ hζ
    (b[f,d]) f d i ε γ
  change cl (sourceKPReflectedNumerator K hζ S₀ f d i ε γ) = _ at hm
  rw [hm]

variable {J : Ideal (𝓞 K)}

def sourceKPReflectedBranchArithmetic
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u ε : X) (h d : E) (f : Finset PE) (i : SourceReflectionTermIndex K S₀ f) (r : L) : ℂ :=
  sourceReflectionExteriorGuardedSeparated K S₀ hζ hS (rep ε)
    h f i.1.val i.2.1 d i.2.2.val *
    (sourceKPPhysicalNegativeScalarPhase K hζ S₀ hS η hJ (rep u) (rep ε) f i.1.val i.2.1 *
      sourceKPPhysicalNegativeRowPhase K hζ S₀ hS η hJ (rep u) d *
      sourceKPPhysicalNegativeColumnPhase K hζ S₀ hS η hJ (rep u) i.2.2.val) *
    sourceKPReflectedClassWeight K hζ S₀ f i.1.val i.2.1 ε (C d) (C i.2.2.val) r

theorem sourceKPReflectedBranchArithmetic_norm_le
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u ε : X) (h d : E) (f : Finset PE) (i : SourceReflectionTermIndex K S₀ f) (r : L) :
    ‖sourceKPReflectedBranchArithmetic K hζ S₀ hS η hJ u ε h d f i r‖ ≤
      sourceReflectionDirichletTerm K S₀ f 0 i :=
  sourceReflectionPhysicalCoefficient_norm_le_dirichlet K S₀ hζ hS η hJ
    (rep u) (rep ε) h d f i (sourceKPReflectedClassWeight_norm_le K hζ S₀ _ _ _ _ _ _ _)

theorem sourceKPReflectedBranchArithmetic_supported
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (hcut : principalAngularCutoff K J ⊆ S)
    (u ε : X) (h d : E) (f : Finset PE)
    (hf : f ∈ sourceReflectionActiveChoices K S₀ h) (hd : sourceReflectionIsSquarefree d)
    (hdh : Disjoint d.support h.support)
    (i : SourceReflectionSupportedTermIndex K S₀ f d) (γ : Γ) (r : L) :
    let b := b[f,d]
    let m := sourceKPReflectedNumerator K hζ S₀ f d i ε γ
    sourceKPReflectedBranchArithmetic K hζ S₀ hS η hJ u ε h d f i.val r =
      sourceReflectionSignedExteriorProduct K S₀ hζ hS (h+d) (f∪d.support) (m/b^2) *
        sourceKPPhysicalNegativePhase K hζ S₀ hS η hJ (rep u) b (D m) *
        sourceKPRetainedNegativeClass K hζ S₀ (cl ((b⁻¹)^2)) (cl m) r := by
  dsimp only
  unfold sourceKPReflectedBranchArithmetic
  rw [sourceKPReflectedNumerator_div,
    sourceReflectionExteriorGuardedSeparated_eq_supported_frequency K S₀ hζ hS h d f hf hd hdh i ε γ,
    sourceKPReflectedClassWeight_supported K hζ S₀ f d i ε γ]
  have hphase := sourceKPPhysicalNegativePhase_supported K hζ S₀ hS η hJ hcut (rep u) f d i ε γ
  dsimp only at hphase
  exact congrArg (fun z : ℂ => _ * z * _) hphase.symm

end
end ArtinMatthews
