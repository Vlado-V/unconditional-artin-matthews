module

public import ArtinMatthews.SourceFrequencyUnitPart
public import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Every nonzero source S-integer is uniquely a fixed exterior
monomial times an actual exterior unit. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

abbrev SourceNonzeroFrequency := {x : sourceRing F S₀ // x ≠ 0}

def sourceFrequencyMonomial (e : SourcePrimeExponents F S₀)
    (u : exteriorUnitSubgroup (sourceHilbertSet F S₀)) : SourceNonzeroFrequency F S₀ :=
  ⟨sourceExteriorUnitToSourceRing F S₀ u * sourcePrimeExponentGenerator F hζ S₀ e,
    mul_ne_zero (sourceExteriorUnitToSourceRing_ne_zero F S₀ u) (sourcePrimeExponentGenerator_ne_zero F hζ S₀ e)⟩

@[simp] theorem sourceFrequencyMonomial_val (e : SourcePrimeExponents F S₀)
    (u : exteriorUnitSubgroup (sourceHilbertSet F S₀)) :
    (sourceFrequencyMonomial F hζ S₀ e u).val =
      sourceExteriorUnitToSourceRing F S₀ u * sourcePrimeExponentGenerator F hζ S₀ e := rfl

theorem sourceFrequencyMonomial_exponents (e : SourcePrimeExponents F S₀)
    (u : exteriorUnitSubgroup (sourceHilbertSet F S₀)) :
    sourceElementExponents F S₀ (sourceFrequencyMonomial F hζ S₀ e u).val
      (sourceFrequencyMonomial F hζ S₀ e u).property = e := by
  change sourceElementExponents F S₀
    (sourceExteriorUnitToSourceRing F S₀ u * sourcePrimeExponentGenerator F hζ S₀ e)
    (mul_ne_zero (sourceExteriorUnitToSourceRing_ne_zero F S₀ u) (sourcePrimeExponentGenerator_ne_zero F hζ S₀ e)) = e
  rw [sourceElementExponents_mul F S₀ _ _ (sourceExteriorUnitToSourceRing_ne_zero F S₀ u)
    (sourcePrimeExponentGenerator_ne_zero F hζ S₀ e),
    sourceExteriorUnitToSourceRing_exponents F S₀ hζ, sourceElementExponents_of_generator F S₀ hζ, zero_add]

def sourceFrequencyMonomialEquiv :
    SourcePrimeExponents F S₀ × exteriorUnitSubgroup (sourceHilbertSet F S₀) ≃ SourceNonzeroFrequency F S₀ :=
  Equiv.ofBijective (fun p => sourceFrequencyMonomial F hζ S₀ p.1 p.2) (by
    constructor
    · rintro ⟨e, u⟩ ⟨f, v⟩ h
      change sourceFrequencyMonomial F hζ S₀ e u = sourceFrequencyMonomial F hζ S₀ f v at h
      have hef : e = f := by
        simpa only [sourceFrequencyMonomial_exponents] using
          congrArg (fun x : SourceNonzeroFrequency F S₀ => sourceElementExponents F S₀ x.val x.property) h
      subst f
      have hv : sourceExteriorUnitToSourceRing F S₀ u * sourcePrimeExponentGenerator F hζ S₀ e =
          sourceExteriorUnitToSourceRing F S₀ v * sourcePrimeExponentGenerator F hζ S₀ e :=
        congrArg Subtype.val h
      exact Prod.ext rfl (sourceExteriorUnitToSourceRing_injective F S₀
        (mul_right_cancel₀ (sourcePrimeExponentGenerator_ne_zero F hζ S₀ e) hv))
    · intro x
      exact ⟨(sourceElementExponents F S₀ x.val x.property, sourceFrequencyUnitPart F S₀ hζ x.val x.property),
        Subtype.ext (sourceFrequencyUnitPart_factor F S₀ hζ x.val x.property)⟩)

@[simp] theorem sourceFrequencyMonomialEquiv_apply (e : SourcePrimeExponents F S₀)
    (u : exteriorUnitSubgroup (sourceHilbertSet F S₀)) :
    sourceFrequencyMonomialEquiv F hζ S₀ (e, u) = sourceFrequencyMonomial F hζ S₀ e u := rfl

end
end ArtinMatthews
