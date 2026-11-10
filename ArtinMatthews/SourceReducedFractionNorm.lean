module

public import ArtinMatthews.SourceReducedFractionLabels
public import ArtinMatthews.SLocalNormAlgebra
public import ArtinMatthews.SourceFrequencyOrbitSeparation
public import ArtinMatthews.SourceFrequencyPoissonArgument
public import ArtinMatthews.SourcePrimeExponentProducts
public import ArtinMatthews.SourcePrimeNormSummability
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact S-product norms of nonzero source integers and literal reduced
fraction separation, uniformly over all balanced denominator choices. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain AllowedGenerators FractionalIdeal
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F}

local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "U" => sourceNonzeroFrequencyFieldUnit F S₀

theorem sourceSInteger_fieldSNorm_eq (hζ : IsPrimitiveRoot ζ 12) (x : R) (hx : x ≠ 0) :
    fieldSNorm F S (U ⟨x, hx⟩) = q (sourceElementExponents F S₀ x hx) := by
  let e := sourceElementExponents F S₀ x hx
  have hI : Ideal.span {x} = Ideal.span {sourcePrimeExponentGenerator F hζ S₀ e} :=
    (sourceElementExponents_ideal F S₀ x hx).symm.trans (sourcePrimeExponentGenerator_ideal F hζ S₀ e)
  have he : toPrincipalIdeal R F (U ⟨x, hx⟩) =
      toPrincipalIdeal R F (sourcePrimeExponentUnit F hζ S₀ e) := by
    apply Units.ext
    rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal, sourceNonzeroFrequencyFieldUnit_val,
      sourcePrimeExponentUnit_val]
    have h := congrArg (fun J : Ideal R => (J : FractionalIdeal R⁰ F)) hI
    rw [coeIdeal_span_singleton, coeIdeal_span_singleton] at h
    exact h
  rw [fieldSNorm_eq_of_principal_eq F S₀ _ _ he, sourcePrimeExponentUnit_fieldSNorm F hζ S₀]

theorem sourceSInteger_one_le_fieldSNorm (hζ : IsPrimitiveRoot ζ 12) (x : R) (hx : x ≠ 0) :
    1 ≤ fieldSNorm F S (U ⟨x, hx⟩) := by
  rw [sourceSInteger_fieldSNorm_eq F S₀ hζ]
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (sourcePrimeExponentNorm_pos F S₀ _).ne')

theorem sourceDenominator_fieldSNorm_eq (hζ : IsPrimitiveRoot ζ 12) (a : E → R) (ha : ∀ e, a e ≠ 0)
    (hgen : ∀ e, (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {a e}) (e : E) :
    fieldSNorm F S (U ⟨a e, ha e⟩) = q e := by
  have he : sourceElementExponents F S₀ (a e) (ha e) = e :=
    (sourcePrimeExponentRingIdealEquiv F S₀).injective (Subtype.ext
      ((sourceElementExponents_ideal F S₀ (a e) (ha e)).trans (hgen e).symm))
  rw [sourceSInteger_fieldSNorm_eq F S₀ hζ, he]

theorem sourceReducedFraction_lifts_difference_ne_zero
    (a : E → R) (ha : ∀ e, a e ≠ 0)
    (hgen : ∀ e, (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {a e})
    (p p' : SourceReducedFractionLabel F S₀ a) (x x' r : R)
    (hx : Ideal.Quotient.mk (Ideal.span {a p.1}) x = (p.2 : R ⧸ Ideal.span {a p.1}))
    (hx' : Ideal.Quotient.mk (Ideal.span {a p'.1}) x' = (p'.2 : R ⧸ Ideal.span {a p'.1}))
    (hne : p ≠ p') :
    (x : F) / (a p.1 : F) - (x' : F) / (a p'.1 : F) + (r : F) ≠ 0 := by
  intro h
  apply hne
  have he := eq_neg_of_add_eq_zero_left h
  exact sourceReducedFraction_eq_of_lifts_sub_eq F S₀ a ha hgen p p' x x' (-r) hx hx' he

/-- This is the exact product-norm separation before any norm cutoff.
The arbitrary source-integer shift and the two true denominator norms
are retained. -/
theorem sourceReducedFraction_lifts_fieldSNorm_lower (hζ : IsPrimitiveRoot ζ 12)
    (a : E → R) (ha : ∀ e, a e ≠ 0)
    (hgen : ∀ e, (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {a e})
    (p p' : SourceReducedFractionLabel F S₀ a) (x x' r : R)
    (hx : Ideal.Quotient.mk (Ideal.span {a p.1}) x = (p.2 : R ⧸ Ideal.span {a p.1}))
    (hx' : Ideal.Quotient.mk (Ideal.span {a p'.1}) x' = (p'.2 : R ⧸ Ideal.span {a p'.1}))
    (hne : p ≠ p') :
    1 / ((q p.1 : ℝ) * (q p'.1 : ℝ)) ≤
      fieldSNorm F S (Units.mk0 _ (sourceReducedFraction_lifts_difference_ne_zero F S₀ a ha hgen
        p p' x x' r hx hx' hne)) := by
  let A := U ⟨a p.1, ha p.1⟩
  let B := U ⟨a p'.1, ha p'.1⟩
  let D := Units.mk0 _ (sourceReducedFraction_lifts_difference_ne_zero F S₀ a ha hgen
    p p' x x' r hx hx' hne)
  let n : R := x * a p'.1 - x' * a p.1 + r * (a p.1 * a p'.1)
  have haF : (a p.1 : F) ≠ 0 := fun h => ha p.1 (Subtype.ext h)
  have hbF : (a p'.1 : F) ≠ 0 := fun h => ha p'.1 (Subtype.ext h)
  have hval : ((D * (A * B) : Fˣ) : F) = (n : F) := by
    change ((x : F) / (a p.1 : F) - (x' : F) / (a p'.1 : F) + (r : F)) *
      ((a p.1 : F) * (a p'.1 : F)) =
        (x : F) * (a p'.1 : F) - (x' : F) * (a p.1 : F) + (r : F) * ((a p.1 : F) * (a p'.1 : F))
    field_simp
  have hn : n ≠ 0 := by
    intro hz
    apply (D * (A * B)).ne_zero
    rw [hval, hz]
    rfl
  have hN : U ⟨n, hn⟩ = D * (A * B) := Units.ext hval.symm
  have hbound := sourceSInteger_one_le_fieldSNorm F S₀ hζ n hn
  rw [hN, map_mul, map_mul] at hbound
  have hA : fieldSNorm F S A = q p.1 := sourceDenominator_fieldSNorm_eq F S₀ hζ a ha hgen p.1
  have hB : fieldSNorm F S B = q p'.1 := sourceDenominator_fieldSNorm_eq F S₀ hζ a ha hgen p'.1
  rw [hA, hB] at hbound
  exact (div_le_iff₀ (mul_pos (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ p.1))
    (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ p'.1)))).mpr hbound

theorem sourceReducedFraction_lifts_fieldSNorm_cutoff (hζ : IsPrimitiveRoot ζ 12)
    (a : E → R) (ha : ∀ e, a e ≠ 0)
    (hgen : ∀ e, (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {a e})
    (p p' : SourceReducedFractionLabel F S₀ a) (x x' r : R)
    (hx : Ideal.Quotient.mk (Ideal.span {a p.1}) x = (p.2 : R ⧸ Ideal.span {a p.1}))
    (hx' : Ideal.Quotient.mk (Ideal.span {a p'.1}) x' = (p'.2 : R ⧸ Ideal.span {a p'.1}))
    (hne : p ≠ p') {V : ℝ}
    (hV : 0 ≤ V) (hp : (q p.1 : ℝ) ≤ V) (hp' : (q p'.1 : ℝ) ≤ V) :
    1 / V ^ 2 ≤ fieldSNorm F S (Units.mk0 _ (sourceReducedFraction_lifts_difference_ne_zero F S₀ a ha hgen
      p p' x x' r hx hx' hne)) := by
  have hpos : 0 < (q p.1 : ℝ) * (q p'.1 : ℝ) :=
    mul_pos (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ p.1))
      (Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ p'.1))
  have hle : (q p.1 : ℝ) * (q p'.1 : ℝ) ≤ V ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hp hp' (Nat.cast_nonneg _) hV
  exact (one_div_le_one_div_of_le hpos hle).trans
    (sourceReducedFraction_lifts_fieldSNorm_lower F S₀ hζ a ha hgen p p' x x' r hx hx' hne)

end
end ArtinMatthews.SourcePhysical
