module

public import ArtinMatthews.SourcePoissonPhysicalPairing
public import ArtinMatthews.SourcePoissonOriginalInitialContour
public import ArtinMatthews.SourceSLocalProbeSheetIdentity
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical VaryingKummerAnalytic QuadraticWeil
open MeasureTheory Filter
open scoped NumberField Classical BigOperators ENNReal
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "D" => sNormOneFundamentalSet F S
local notation "ν" => sourceSLocalNormalizedSheetMeasure F hζ S v
local notation "μ" => sNormOneQuotientMeasure F S ν

/-- Apply the two actual second moments on any finite set containing
the support of the additive factor at the chosen representative. -/
theorem sourcePoissonOriginalDensity_norm_le_square_moments
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (X : ℝ) {Y Z : ℝ} (hY : 0 < Y) (hZ : 0 < Z) (t : SNormOne F S)
    (M : Finset R)
    (hM : ∀ m ∉ M, sourcePoissonPhysicalAdditiveFactor F S₀ hζ X Y t m = 0)
    (A B : ℝ)
    (hA : ∑ m ∈ M, ‖sourcePoissonPhysicalAdditiveFactor F S₀ hζ X Y t m‖ ^ 2 ≤ A)
    (hB : ∑ m ∈ M, ‖reflectionCoefficientRow F hζ S₀ hBad η m Z‖ ^ 2 ≤ B) :
    ‖sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z t‖ ≤ Real.sqrt A * Real.sqrt B := by
  let g := sourcePoissonPhysicalAdditiveFactor F S₀ hζ X Y t
  let b (m : R) := reflectionCoefficientRow F hζ S₀ hBad η m Z
  rw [sourcePoissonOriginalDensity_eq_additivePairing F S₀ hζ η hBad X hY hZ t]
  change ‖∑' m : R, g m * b m‖ ≤ _
  rw [tsum_eq_sum (s := M)]
  · calc
      _ ≤ ∑ m ∈ M, ‖g m * b m‖ := norm_sum_le _ _
      _ = ∑ m ∈ M, ‖g m‖ * ‖b m‖ := Finset.sum_congr rfl fun _ _ => norm_mul _ _
      _ ≤ Real.sqrt (∑ m ∈ M, ‖g m‖ ^ 2) * Real.sqrt (∑ m ∈ M, ‖b m‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt M _ _
      _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · intro m hm
    exact mul_eq_zero_of_left (hM m hm) (b m)

/-- Uniform moment bounds on the actual bounded fundamental representatives
give the physical probe bound with the exact quotient-volume factor. -/
theorem sourcePoissonOriginalIntegral_norm_le_square_moments
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (A B : ℝ)
    (hMom : ∀ t : SNormOne F S, t ∈ D →
      ∃ M : Finset R,
        (∀ m ∉ M, sourcePoissonPhysicalAdditiveFactor F S₀ hζ X Y t m = 0) ∧
        (∑ m ∈ M, ‖sourcePoissonPhysicalAdditiveFactor F S₀ hζ X Y t m‖ ^ 2 ≤ A) ∧
        (∑ m ∈ M, ‖reflectionCoefficientRow F hζ S₀ hBad η m Z‖ ^ 2 ≤ B)) :
    ‖sourcePoissonOriginalIntegral F S₀ hζ η v hBad X Y Z‖ ≤
      (Real.sqrt A * Real.sqrt B) * (ν).real D := by
  let f := sourcePoissonOriginalQuotientDensity F S₀ hζ η hBad X Y Z
  have hf : Integrable f μ :=
    (sourcePoissonOriginalIntegral_eq_actualOrbitSeries F S₀ hζ η v hBad hX hY hZ).1
  let : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar F hζ S v
  have hD := (sNormOneFundamentalSet_spec F S).1
  have hF : ν D < ∞ :=
    (measure_mono (sNormOneFundamentalSet_spec F S).2.1).trans_lt
      (sNormOneCover_isCompact F S).measure_lt_top
  let : IsFiniteMeasure ((ν).restrict D) := ⟨by simpa only [Measure.restrict_apply_univ] using hF⟩
  have hBound :
      ∀ᵐ t ∂(ν).restrict D, ‖f (sNormOneSixthQuotientMap F S t)‖ ≤ Real.sqrt A * Real.sqrt B := by
    apply (ae_restrict_iff' hD).mpr
    filter_upwards with t ht
    obtain ⟨M, hM, hA, hB⟩ := hMom t ht
    rw [show f (sNormOneSixthQuotientMap F S t) =
        sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z t from
      sourcePoissonOriginalQuotientDensity_mk F S₀ hζ η hBad X Y Z t]
    exact sourcePoissonOriginalDensity_norm_le_square_moments F S₀ hζ η hBad X hY hZ
      t M hM A B hA hB
  change ‖∫ t, f t ∂μ‖ ≤ _
  rw [sNormOneQuotient_integral F S ν f hf]
  simpa only [measureReal_def, Measure.restrict_apply_univ] using
    norm_integral_le_of_norm_le_const hBound

end
end ArtinMatthews.SourceEulerAssembly
