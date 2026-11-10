module

public import ArtinMatthews.SourceKPReflectedBranchArithmetic
public import ArtinMatthews.SourceKPReflectedRetainedProfiles
public import ArtinMatthews.SourceReflectionPhysicalProfiles
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

/-! The actual finite reflected profiles and class slices give the
coefficient data used by the reflected moment. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain QuadraticWeil VaryingKummerAnalytic AllowedGenerators
open SourceEulerAssembly SourcePhysical SourceReflection
open scoped NumberField Classical ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "Pr" => SourceExteriorPrime K S₀
local notation "X" => ExteriorUnitSixthClasses (K := K) S
local notation "Q" => SWholePowerClasses K 6 S
local notation "C" => sourceReflectionExponentSixthClass K S₀ hζ
local notation "rep" => sourceExteriorUnitSixthRepresentative (F := K) S

abbrev SourceReflectionActualBranchLabel (R M : ↥(sourceHilbertSet K S₀) → ℕ) :=
  X × SourceKPReflectedRetainedLabel K hζ S₀ R M

variable {J : Ideal (𝓞 K)} {T : ℝ}
variable (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
variable (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (hT : 2 < T)
variable (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
variable (u : ExteriorUnitSixthClasses (K := K) (sourceHilbertSet K S₀)) (v : InfinitePlace K)

local notation "Label" => SourceReflectionActualBranchLabel K hζ S₀ p.R p.M
local notation "Retained" => SourceKPReflectedRetainedLabel K hζ S₀ p.R p.M
local notation "P" => sourceKPReflectedRetainedScaledProfile K hζ S₀ hS η hJ hT p u v

def sourceReflectionLiteralActualData : SourceReflectionExpansionData K S₀ (Label × Q × Q) := by
  letI : Fintype Retained := sourceKPReflectedRetainedLabel_fintype K hζ S₀ p.R p.M
  have hP := sourceKPReflectedRetainedScaledProfile_inputs K hζ S₀ hS η hJ hT p u v
  exact sourceReflectionExpansionData_of_physicalProfiles K S₀ hζ hS η hJ (rep u)
    (fun j => j.1.1)
    (fun _ f a n j => sourceKPReflectedClassWeight K hζ S₀ f a n j.1.1 j.2.1 j.2.2 j.1.2.2.2)
    (fun _ f a n j => sourceKPReflectedClassWeight_norm_le K hζ S₀ f a n
      j.1.1 j.2.1 j.2.2 j.1.2.2.2)
    P (fun _ _ _ _ j => some j.1.2) hP.1 hP.2

local notation "A" => sourceReflectionLiteralActualData K hζ S₀ hS η hJ hT p u v

theorem sourceReflectionLiteralActualData_term (Z : ℝ) (h d : E) (f : Finset Pr)
    (i : SourceReflectionTermIndex K S₀ f) (j : Label) :
    sourceReflectionExpansionTerm K S₀ hζ A Z h d f i.1.val i.2.1 i.2.2.val
      (j, C d, C i.2.2.val) =
      sourceKPReflectedBranchArithmetic K hζ S₀ hS η hJ u j.1 h d f i j.2.2.2 *
        P (some j.2) (sourceReflectionTermLength K S₀ i.1.val i.2.1 i.2.2.val /
          sourceReflectionTermScale K S₀ Z f d) := by
  unfold sourceReflectionLiteralActualData sourceReflectionExpansionData_of_physicalProfiles
  rw [sourceReflectionExpansionTerm_of_exteriorProfiles]
  unfold sourceKPReflectedBranchArithmetic
  ring

theorem sourceReflectionLiteralActualData_term_zero (Z : ℝ) (h d : E) (f : Finset Pr)
    (i : SourceReflectionTermIndex K S₀ f) (j : Label)
    (hi : ¬ sourceReflectionTermSupported K S₀ f d i) :
    sourceReflectionExpansionTerm K S₀ hζ A Z h d f i.1.val i.2.1 i.2.2.val
      (j, C d, C i.2.2.val) = 0 := by
  rw [sourceReflectionLiteralActualData_term]
  unfold sourceKPReflectedBranchArithmetic
  rw [sourceReflectionExteriorGuardedSeparated_zero_of_unsupported K S₀ hζ hS
      (rep j.1) h d f i hi, zero_mul, zero_mul, zero_mul]

end
end ArtinMatthews
