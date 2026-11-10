module

public import ArtinMatthews.SourceReflectionExteriorProfiles
public import ArtinMatthews.SourceKPPhysicalNegativePhase
public import ArtinMatthews.SourceKPPhysicalNegativePhaseSupported
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

/-! The bounded factors are the actual signed exterior coefficient and
the actual normalized row phase. Only the finite radial profile is
selected by the retained Jacquet and class labels. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain AllowedGenerators QuadraticWeil VaryingKummerAnalytic
open SourcePhysical
open scoped NumberField Classical ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
variable (u : exteriorUnitSubgroup (sourceHilbertSet F S₀))
variable {U V : Type} [Fintype V] [Nonempty V]
variable (frequencyClass : U → ExteriorUnitSixthClasses (K := F) (sourceHilbertSet F S₀))
variable (κ : SourcePrimeExponents F S₀ → Finset (SourceExteriorPrime F S₀) →
  SourcePrimeExponents F S₀ → SourcePrimeExponents F S₀ → U → ℂ)
variable (hκ : ∀ h f a n j, ‖κ h f a n j‖ ≤ 1)
variable (P : V → ℝ → ℂ)
variable (index : SourcePrimeExponents F S₀ → Finset (SourceExteriorPrime F S₀) →
  SourcePrimeExponents F S₀ → SourcePrimeExponents F S₀ → U → V)
variable (hsmooth : ∀ v : V, ContDiff ℝ ∞ (fun x : ℝ => P v (Real.exp x)))
variable (hP : ∀ v : V, ∃ α : ℝ, 0 ≤ α ∧ ∀ A : ℝ, 0 < A →
  ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 2, ∀ x : ℝ,
    ‖iteratedFDeriv ℝ k (fun y => P v (Real.exp y)) x‖ ≤
      M * min (Real.exp (α * x)) (Real.exp (-A * x)))

local notation "E" => SourcePrimeExponents F S₀
local notation "Prime" => SourceExteriorPrime F S₀
local notation "S" => sourceHilbertSet F S₀
local notation "rep" => sourceExteriorUnitSixthRepresentative (F := F) S
local notation "sp" => sourceKPPhysicalNegativeScalarPhase F hζ S₀ hS η hJ u
local notation "rp" => sourceKPPhysicalNegativeRowPhase F hζ S₀ hS η hJ u
local notation "cp" => sourceKPPhysicalNegativeColumnPhase F hζ S₀ hS η hJ u

def sourceReflectionExpansionData_of_physicalProfiles : SourceReflectionExpansionData F S₀ U :=
  sourceReflectionExpansionData_of_exteriorProfiles F S₀ hζ hS (fun j => rep (frequencyClass j))
    (fun h f a n j => sp (rep (frequencyClass j)) f a n * κ h f a n j)
    (fun _ _ _ _ _ d => rp d)
    (fun _ _ _ _ _ c => cp c)
    P index
    (fun h f a n j => by
      rw [norm_mul, sourceKPPhysicalNegativeScalarPhase_norm, one_mul]
      exact hκ h f a n j)
    (fun _ _ _ _ _ d => (sourceKPPhysicalNegativeRowPhase_norm F hζ S₀ hS η hJ u d).le)
    (fun _ _ _ _ _ c => (sourceKPPhysicalNegativeColumnPhase_norm F hζ S₀ hS η hJ u c).le)
    hsmooth hP

local notation "A" => sourceReflectionExpansionData_of_physicalProfiles F S₀ hζ hS η hJ u
  frequencyClass κ hκ P index hsmooth hP

theorem sourceReflectionExpansionTerm_of_physicalProfiles_zero (Z : ℝ) (h d : E)
    (f : Finset Prime) (i : SourceReflectionTermIndex F S₀ f) (j : U)
    (hi : ¬ sourceReflectionTermSupported F S₀ f d i) :
    sourceReflectionExpansionTerm F S₀ hζ A Z h d f i.1.val i.2.1 i.2.2.val j = 0 := by
  unfold sourceReflectionExpansionData_of_physicalProfiles
  exact sourceReflectionExpansionTerm_of_exteriorProfiles_zero F S₀ hζ hS _ _ _ _ P index
    _ _ _ hsmooth hP Z h d f i j hi

theorem sourceReflectionExpansionTerm_of_physicalProfiles
    (hcut : principalAngularCutoff F J ⊆ S)
    (Z : ℝ) (h d : E) (f : Finset Prime)
    (hf : f ∈ sourceReflectionActiveChoices F S₀ h)
    (hd : sourceReflectionIsSquarefree d) (hdh : Disjoint d.support h.support)
    (i : SourceReflectionSupportedTermIndex F S₀ f d) (j : U) (γ : sNormOneSixthSubgroup F S) :
    let b := sourcePrimeExponentUnit F hζ S₀ (sourceReflectionActiveExponents F S₀ f + d)
    let ν := (sourceReflectionSupportedFrequencyEquiv F S₀ hζ b f d (i,frequencyClass j,γ)).val.val
    sourceReflectionExpansionTerm F S₀ hζ A Z h d f i.val.1.val i.val.2.1 i.val.2.2.val j =
      sourceReflectionSignedExteriorProduct F S₀ hζ hS (h+d) (f∪d.support) ν *
        sourceKPPhysicalNegativePhase F hζ S₀ hS η hJ u b (sWholeDiagonal F S (ν*b^2)) *
        κ h f i.val.1.val i.val.2.1 j * P (index h f i.val.1.val i.val.2.1 j)
          (sourceReflectionTermLength F S₀ i.val.1.val i.val.2.1 i.val.2.2.val /
            sourceReflectionTermScale F S₀ Z f d) := by
  dsimp only
  unfold sourceReflectionExpansionData_of_physicalProfiles
  rw [sourceReflectionExpansionTerm_of_exteriorProfiles,
    sourceReflectionExteriorGuardedSeparated_eq_supported_frequency F S₀ hζ hS
      h d f hf hd hdh i (frequencyClass j) γ,
    sourceKPPhysicalNegativePhase_supported F hζ S₀ hS η hJ hcut u f d i (frequencyClass j) γ]
  ring

end
end ArtinMatthews.SourceEulerAssembly
