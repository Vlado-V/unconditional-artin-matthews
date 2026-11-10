module

public import ArtinMatthews.SourceThetaRotatedSheetBounds
public import ArtinMatthews.SourceSLocalProbeSheetIdentity
public import ArtinMatthews.SourceSLocalRadialHomeomorph
public import ArtinMatthews.SourceSLocalRadialInvariance
public import ArtinMatthews.SourceThetaRotatedSheetMass
public import ArtinMatthews.StandardLocalBall
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

/-! Bounded measurable phase and class factors preserve the absolute
sheet bound and give measurable signed profiles in the log radius. -/
namespace ArtinMatthews.SourceReflection

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory SourcePhysical
open scoped NumberField ENNReal
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {ζ : K} {hζ : IsPrimitiveRoot ζ 12} {v : InfinitePlace K} {δ : ℝ}
local notation "hv" => sourceSLocalComplexPlace K hζ v
local notation "U" => SWholeUnits K S
local notation "Y" => SNormOne K S
local notation "ν" => sourceSLocalNormalizedSheetMeasure K hζ S v

theorem sourceSLocalSheetProfile_log_measurable (F : U → ℂ) (hF : Measurable F) :
    Measurable (fun t : ℝ => sourceSLocalSheetProfile S ν hζ F (Real.exp t)) := by
  have : BorelSpace U := sourceSWholeUnits_product_borel S v
  have : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  have : SigmaFinite ν := sourceSLocalNormalizedSheetMeasure_sigmaFinite K hζ S v
  let G (p : ℝ × Y) := F ((p.2 : U) * sourceSLocalRadial hv S p.1)
  have hG : Measurable G := hF.comp
    (((continuous_subtype_val.comp continuous_snd).mul
      ((sourceSLocalRadial_continuous hv S).comp continuous_fst)).measurable)
  have hm : Measurable (fun t => ∫ x : Y, G (t,x) ∂ν) :=
    (StronglyMeasurable.integral_prod_right' hG.stronglyMeasurable).measurable
  have he : (fun t => ∫ x : Y, G (t,x) ∂ν) =
      fun t : ℝ => sourceSLocalSheetProfile S ν hζ F (Real.exp t) :=
    funext (sourceSLocal_radial_integral_eq_literal S ν hζ hv F)
  exact he ▸ hm

namespace SourceThetaRotatedTensor

variable (d : SourceThetaRotatedTensor K S hζ v δ)
variable (j : ℕ)

def weightedSheet (w : U → ℂ) : ℝ → ℂ :=
  sourceSLocalSheetProfile S ν hζ
    (fun x => w x * sourceThetaSLocalTensor K S hζ v (d.localDeriv j) d.retained x)

theorem weightedSheet_log_measurable (w : U → ℂ) (hw : Measurable w) :
    Measurable (fun t : ℝ => d.weightedSheet j w (Real.exp t)) :=
  sourceSLocalSheetProfile_log_measurable _ (hw.mul (d.tensor_measurable j))

theorem weightedSheet_norm_bound (σ : ℝ) (hσ : -δ < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : U → ℂ), (∀ x, ‖w x‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → ‖d.weightedSheet j w T‖ ≤ C * T^(-σ) := by
  obtain ⟨C,hC,hb⟩ := d.scaled_tensor_mass j σ hσ
  refine ⟨C,hC,fun w hw T hT => ?_⟩
  let u := sLocalPositiveScaling K hζ S T
  let F := sourceThetaSLocalTensor K S hζ v (d.localDeriv j) d.retained
  have h := hb u
  rw [sLocalPositiveScaling_norm K hζ S hT] at h
  have hpoint (x : Y) : ‖w ((x : U)*u) * F ((x : U)*u)‖ₑ ≤ ‖F ((x : U)*u)‖ₑ := by
    rw [enorm_mul]
    have hw' : ‖w ((x : U)*u)‖ₑ ≤ 1 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (hw _)
    exact mul_le_of_le_one_left' hw'
  have hInt := (enorm_integral_le_lintegral_enorm
    (μ := ν) (fun x : Y => w ((x : U)*u) * F ((x : U)*u))).trans
      ((lintegral_mono hpoint).trans h)
  rw [← ofReal_norm] at hInt
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (Real.rpow_nonneg hT.le _))).mp hInt

end SourceThetaRotatedTensor
end
end ArtinMatthews.SourceReflection
