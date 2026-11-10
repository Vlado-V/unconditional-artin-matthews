module

public import ArtinMatthews.SourceReflectionClassSlices
public import ArtinMatthews.SourceReflectionActiveBranchReindex
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

/-! Assemble the literal coefficient from its active branches and their
supported frequency expansions. The class masks become the separate
row and column factors required by the reflected moment. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (hBad : QuadraticWeil.standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {U : Type} [Fintype U]

local notation "E" => SourcePrimeExponents F S₀
local notation "Prime" => SourceExteriorPrime F S₀
local notation "S" => sourceHilbertSet F S₀
local notation "Q" => SWholePowerClasses F 6 S
local notation "Classes" => ExteriorUnitSixthClasses (K := F) S
local notation "C" => sourceReflectionExponentSixthClass F S₀ hζ
local notation "T" => sourceReflectionExpansionTerm F S₀ hζ
local notation "H" => sourceReflectionPowerfulPart
local notation "D" => sourceReflectionSimplePart
local notation "Active" => sourceReflectionActiveChoices F S₀

variable [Fintype (SWholePowerClasses F 6 (sourceHilbertSet F S₀))]

theorem sourceReflectionLiteralExpansion_of_supportedBranches
    (A : Classes → SourceReflectionExpansionData F S₀ (U × Q × Q))
    (B : ℝ → E → Classes → Finset Prime → ℂ)
    (hrow : ∀ Z : ℝ, 0 < Z → ∀ (e : E) (u : Classes),
      reflectionCoefficientRow F hζ S₀ hBad η (sourceReflectionCanonicalRow F S₀ hζ e u) Z =
        ∑ g ∈ e.support.powerset, B Z e u g)
    (hinactive : ∀ Z : ℝ, 0 < Z → ∀ (e : E) (u : Classes) (g : Finset Prime),
      g ∈ e.support.powerset → g ∉ Active e → B Z e u g = 0)
    (hbranch : ∀ Z : ℝ, 0 < Z → ∀ (e : E) (u : Classes) (f : Finset Prime),
      f ∈ Active (H e) →
      B Z e u (f ∪ (D e).support) = ∑' i : SourceReflectionSupportedTermIndex F S₀ f (D e),
        ∑ j : U, T (A u) Z (H e) (D e) f i.val.1.val i.val.2.1 i.val.2.2.val
          (j, C (D e), C i.val.2.2.val))
    (hzero : ∀ Z : ℝ, 0 < Z → ∀ (e : E) (u : Classes) (f : Finset Prime),
      f ∈ Active (H e) →
      ∀ i : SourceReflectionTermIndex F S₀ f, ¬ sourceReflectionTermSupported F S₀ f (D e) i →
      ∀ j : U, T (A u) Z (H e) (D e) f i.1.val i.2.1 i.2.2.val
        (j, C (D e), C i.2.2.val) = 0) :
    SourceReflectionLiteralExpansion F S₀ hζ η hBad
      (fun u => sourceReflectionExpansionData_withClassSlices F S₀ hζ (A u)) := by
  intro Z hZ e u
  rw [hrow Z hZ e u, sourceReflectionActiveBranch_sum_powerfulSimple F S₀ e
    (B Z e u) (hinactive Z hZ e u), sourceReflectionSelectedRow]
  apply Finset.sum_congr rfl
  intro f hf
  rw [sourceReflectionSelectedBranch_sum_supportedClassSlices F S₀ hζ (A u) hZ
    (H e) (D e) f (hzero Z hZ e u f hf)]
  exact hbranch Z hZ e u f hf

end
end ArtinMatthews.SourceEulerAssembly
