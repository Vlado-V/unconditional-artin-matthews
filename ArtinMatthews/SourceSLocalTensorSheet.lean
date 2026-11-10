module

public import ArtinMatthews.SourceSLocalSheetHaar
public import ArtinMatthews.SLocalPositiveScaling
public import ArtinMatthews.SourceComplexPlaceUnitHaar
public import ArtinMatthews.SourceSheetProfile
public import ArtinMatthews.SourceSLocalRadialInvariance
public import ArtinMatthews.SourceSLocalRadialSheet
public import ArtinMatthews.SourceSheetSmooth
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
public import Mathlib.NumberTheory.SelbergSieve
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

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory Set
open scoped NumberField Classical SchwartzMap ContDiff
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {v : InfinitePlace K} (hv : IsComplex v)

def sourceSLocalChosenTensor (g : 𝓢(ℂ, ℂ)) (G : (SNormOneOtherUnits S v) → ℂ) (x : SWholeUnits K S) : ℂ :=
  g (sourceComplexPlaceUnitsEquiv hv (x.1 v) : ℂ) * G (sourceSheetOther S v x)

variable [MeasurableSpace (SNormOneOtherUnits S v)] [BorelSpace (SNormOneOtherUnits S v)]

/-- The literal physical sheet for the split local tensor, using the original all-place ell_T. -/
def sourceSLocalTensorSheet (μo : Measure (SNormOneOtherUnits S v)) {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (g : 𝓢(ℂ, ℂ)) (G : (SNormOneOtherUnits S v) → ℂ) (T : ℝ) : ℂ :=
  ∫ x : SNormOne K S, sourceSLocalChosenTensor S hv g G
    ((x : SWholeUnits K S) * sLocalPositiveScaling K hζ S T)
      ∂sourceSNormOneSheetMeasure S hv (sourceCircleHaar.prod μo)

theorem sourceSLocalTensorSheet_exp (μo : Measure (SNormOneOtherUnits S v)) [μo.IsHaarMeasure]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (g : 𝓢(ℂ, ℂ)) (G : (SNormOneOtherUnits S v) → ℂ) (t : ℝ) :
    sourceSLocalTensorSheet S hv μo hζ g G (Real.exp t) =
      sourceSheetLogProfile μo (sourceSheetOtherNorm S v) g G t := by
  have : sourceCircleHaar.IsHaarMeasure := sourceCircleHaar_isHaar
  have : (sourceSNormOneSheetMeasure S hv (sourceCircleHaar.prod μo)).IsHaarMeasure :=
    sourceSNormOneSheetMeasure_prod_isHaar S hv sourceCircleHaar μo
  unfold sourceSLocalTensorSheet
  rw [← sourceSLocal_radial_integral_eq_literal S _ hζ hv (sourceSLocalChosenTensor S hv g G),
    sourceSNormOneSheetMeasure_integral]
  unfold sourceSheetLogProfile
  apply integral_congr_ae
  filter_upwards with a
  change sourceSLocalChosenTensor S hv g G (sourceSLocalRadialSheet S hv a t) =
    sourceSheetProfileIntegrand (sourceSheetOtherNorm S v) g G t a
  rw [sourceSLocalChosenTensor, sourceSLocalRadialSheet_chosen, sourceSLocalRadialSheet_other,
    sourceSheetProfileIntegrand]

theorem sourceSLocalTensorSheet_logSmooth (μo : Measure (SNormOneOtherUnits S v)) [μo.IsHaarMeasure] [SFinite μo]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (g : 𝓢(ℂ, ℂ)) (G : (SNormOneOtherUnits S v) → ℂ) (hG : Measurable G)
    (σ : ℝ) (hσ : 0 < σ) (hI : Integrable (fun y => ‖G y‖ * (sourceSheetOtherNorm S v y) ^ σ) μo) :
    ContDiff ℝ ∞ (fun t : ℝ => sourceSLocalTensorSheet S hv μo hζ g G (Real.exp t)) := by
  simp_rw [sourceSLocalTensorSheet_exp]
  exact sourceSheetLogProfile_contDiff μo (sourceSheetOtherNorm S v) (sourceSheetOtherNorm_pos S v)
    (measurable_sourceSheetOtherNorm S v) g G hG σ hσ hI

theorem sourceSLocalTensorSheet_norm_le (μo : Measure (SNormOneOtherUnits S v)) [μo.IsHaarMeasure] [SFinite μo]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (g : 𝓢(ℂ, ℂ)) (G : (SNormOneOtherUnits S v) → ℂ) (hG : Measurable G)
    (σ : ℝ) (hσ : 0 < σ) (hI : Integrable (fun y => ‖G y‖ * (sourceSheetOtherNorm S v y) ^ σ) μo) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      ‖sourceSLocalTensorSheet S hv μo hζ g G T‖ ≤ C * T ^ (-σ) := by
  obtain ⟨C,hC,hb⟩ := (sourceSheetLogProfile_integrable_and_bound μo
    (sourceSheetOtherNorm S v) (sourceSheetOtherNorm_pos S v) (measurable_sourceSheetOtherNorm S v)
    g G hG σ hσ hI).2
  refine ⟨C,hC,fun T hT => ?_⟩
  have h := hb (Real.log T)
  rw [← sourceSLocalTensorSheet_exp S hv μo hζ g G, Real.exp_log hT] at h
  rw [Real.rpow_def_of_pos hT, mul_comm (Real.log T)]
  exact h

end
end ArtinMatthews.SourcePhysical
