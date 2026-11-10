module

public import ArtinMatthews.SourceReflectionExteriorGuards
public import ArtinMatthews.SourceReflectionFiniteProfiles
public import ArtinMatthews.SourceReflectionExteriorBounds
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

/-! The actual guarded exterior factors absorb only bounded phases.
The remaining finite family supplies the radial profiles. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain AllowedGenerators QuadraticWeil
open scoped NumberField Classical BigOperators ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {U V : Type} [Fintype V] [Nonempty V]

local notation "E" => SourcePrimeExponents F S₀
local notation "Prime" => SourceExteriorPrime F S₀
local notation "T" => sourceReflectionExpansionTerm F S₀ hζ

variable (ε : U → exteriorUnitSubgroup (sourceHilbertSet F S₀))
variable (scalarPhase : SourcePrimeExponents F S₀ → Finset (SourceExteriorPrime F S₀) →
  SourcePrimeExponents F S₀ → SourcePrimeExponents F S₀ → U → ℂ)
variable (rowPhase columnPhase : SourcePrimeExponents F S₀ → Finset (SourceExteriorPrime F S₀) →
  SourcePrimeExponents F S₀ → SourcePrimeExponents F S₀ → U → SourcePrimeExponents F S₀ → ℂ)
variable (P : V → ℝ → ℂ)
variable (index : SourcePrimeExponents F S₀ → Finset (SourceExteriorPrime F S₀) →
  SourcePrimeExponents F S₀ → SourcePrimeExponents F S₀ → U → V)
variable (hs : ∀ h f a n j, ‖scalarPhase h f a n j‖ ≤ 1)
variable (hr : ∀ h f a n j d, ‖rowPhase h f a n j d‖ ≤ 1)
variable (hc : ∀ h f a n j c, ‖columnPhase h f a n j c‖ ≤ 1)
variable (hsmooth : ∀ v : V, ContDiff ℝ ∞ (fun x : ℝ => P v (Real.exp x)))
variable (hP : ∀ v : V, ∃ α : ℝ, 0 ≤ α ∧ ∀ A : ℝ, 0 < A →
  ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 2, ∀ x : ℝ,
    ‖iteratedFDeriv ℝ k (fun y => P v (Real.exp y)) x‖ ≤
      M * min (Real.exp (α * x)) (Real.exp (-A * x)))

def sourceReflectionExpansionData_of_exteriorProfiles :
    SourceReflectionExpansionData F S₀ U :=
  sourceReflectionExpansionData_of_finiteProfiles F S₀
    (fun h f a n j => sourceReflectionExteriorGuardedFrozen F S₀ hζ hBad (ε j) h f a n *
      scalarPhase h f a n j)
    (fun h f a n j d => sourceReflectionExteriorGuardedRow F S₀ hζ hBad (ε j) h f a n d *
      rowPhase h f a n j d)
    (fun h f a n j c => sourceReflectionExteriorColumn F S₀ hζ (ε j) h f a c *
      columnPhase h f a n j c)
    P index
    (fun h f a n j => by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hs h f a n j)).trans
        (sourceReflectionExteriorGuardedFrozen_norm_le F S₀ hζ hBad (ε j) h f a n))
    (fun h f a n j d => by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hr h f a n j d)).trans
        (sourceReflectionExteriorGuardedRow_norm_le_one F S₀ hζ hBad (ε j) h f a n d))
    (fun h f a n j c => by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hc h f a n j c)).trans
        (sourceReflectionExteriorColumn_norm_le_one F S₀ hζ hBad (ε j) h f a c))
    hsmooth hP

local notation "A" => sourceReflectionExpansionData_of_exteriorProfiles F S₀ hζ hBad
  ε scalarPhase rowPhase columnPhase P index hs hr hc hsmooth hP

theorem sourceReflectionExpansionTerm_of_exteriorProfiles (Z : ℝ) (h d : E)
    (f : Finset Prime) (a n c : E) (j : U) :
    T A Z h d f a n c j =
      sourceReflectionExteriorGuardedSeparated F S₀ hζ hBad (ε j) h f a n d c *
        (scalarPhase h f a n j * rowPhase h f a n j d * columnPhase h f a n j c) *
        P (index h f a n j)
          (sourceReflectionTermLength F S₀ a n c / sourceReflectionTermScale F S₀ Z f d) := by
  simp only [sourceReflectionExpansionTerm, sourceReflectionColumnCoefficient,
    sourceReflectionExpansionData_of_exteriorProfiles, sourceReflectionExpansionData_of_finiteProfiles,
    sourceReflectionExteriorGuardedSeparated, div_eq_mul_inv, mul_inv_rev]
  ring

theorem sourceReflectionExpansionTerm_of_exteriorProfiles_zero (Z : ℝ) (h d : E)
    (f : Finset Prime) (i : SourceReflectionTermIndex F S₀ f) (j : U)
    (hi : ¬ sourceReflectionTermSupported F S₀ f d i) :
    T A Z h d f i.1.val i.2.1 i.2.2.val j = 0 := by
  rw [sourceReflectionExpansionTerm_of_exteriorProfiles,
    sourceReflectionExteriorGuardedSeparated_zero_of_unsupported F S₀ hζ hBad
      (ε j) h d f i hi, zero_mul, zero_mul]

end
end ArtinMatthews.SourceEulerAssembly
