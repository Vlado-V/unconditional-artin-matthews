module

public import ArtinMatthews.SourceSLocalQuotientSheet
public import ArtinMatthews.SourceThetaPositiveSheet
public import ArtinMatthews.SourceKPPositiveTensorMass
public import ArtinMatthews.SourceSLocalProbeSheetIdentity
public import ArtinMatthews.SourceSLocalQuotientOrbitExpansion
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

/-! The literal positive tensor series unfolds on the quotient with its
actual Haar measure and absolute mass. -/
namespace ArtinMatthews.SourceReflection
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory SourcePhysical
open scoped NumberField Classical ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace K)
variable (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w)
variable (U : ∀ p : S, SourceThetaFiniteCutoff K p.val)
local notation "Whole" => SWholeUnits K S
local notation "N" => SNormOne K S
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "ν" => sourceSLocalNormalizedSheetMeasure K hζ S v
local notation "F" => sourceThetaPositiveTensor K S c U
local notation "H" => sourceThetaPositiveSheet K S c U hζ v
local notation "sc" => sLocalPositiveScaling K hζ S

variable {ι : Type} [Countable ι]

include hc in
theorem sourceKPPositiveQuotientSeries_absoluteMass
    (a : ι → ℂ) (u : ι → Whole)
    (ha : Summable (fun i => ‖a i‖ * sLocalNorm K S (u i) ^ (-2 : ℝ)))
    {T : ℝ} (hT : 0 < T) :
    (∑' i, ∫⁻ x : N, ‖a i * F (((x : Whole)*sc T)*u i)‖ₑ ∂ν) < ⊤ := by
  obtain ⟨C,hC,hBound⟩ := sourceThetaPositiveTensor_scaled_mass K S c hc U hζ v 2 (by norm_num)
  let q (i : ι) := sLocalNorm K S (u i)
  let B := C*T^(-2:ℝ)
  have hB : 0 ≤ B := mul_nonneg hC (Real.rpow_nonneg hT.le _)
  have hsum : Summable (fun i => B * (‖a i‖ * q i ^ (-2 : ℝ))) := ha.mul_left B
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (g := fun i =>
    ENNReal.ofReal (B * (‖a i‖ * q i ^ (-2 : ℝ)))) _) hsum.tsum_ofReal_lt_top
  intro i
  let w := sc T*u i
  have hw : sLocalNorm K S w = T * q i := by
    rw [sLocalNorm_mul,sLocalPositiveScaling_norm K hζ S hT]
  have hwi := hBound w
  rw [hw, Real.mul_rpow hT.le (sLocalNorm_pos K S (u i)).le] at hwi
  change (∫⁻ x : N, ‖a i * F (((x : Whole)*sc T)*u i)‖ₑ ∂ν) ≤ _
  simp_rw [mul_assoc (a := _), enorm_mul]
  rw [lintegral_const_mul _ (sourceThetaPositiveTensor_scaled_measurable K S c hc U hζ v w).enorm]
  calc
    _ ≤ ‖a i‖ₑ * ENNReal.ofReal (C * (T ^ (-2 : ℝ) * q i ^ (-2 : ℝ))) := by gcongr
    _ = _ := by
      rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      congr 1
      unfold B
      ring

include hc in
theorem sourceKPPositiveQuotientSeries_unfold
    (a : ι → ℂ) (u : ι → Whole) (P : Whole → ℂ)
    (hP : sourceSLocalSixthInvariant S P)
    (h : ∀ x : Whole, HasSum (fun p : ι × Γ => a p.1 * F ((x*(p.2.val : Whole))*u p.1)) (P x))
    (ha : Summable (fun i => ‖a i‖ * sLocalNorm K S (u i)^(-2:ℝ)))
    {T : ℝ} (hT : 0 < T) :
    Integrable (sourceSLocalQuotientSheetFunction S hζ P hP T) (sNormOneQuotientMeasure K S ν) ∧
      sourceSLocalQuotientSheetProfile S hζ ν P hP T =
        ∑' i, a i * H (T*sLocalNorm K S (u i)) := by
  let : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  let A (i : ι) (x : Whole) := a i * F x
  have hm (i : ι) : Measurable (fun x : N => A i (((x : Whole)*sc T)*u i)) := by
    change Measurable (fun x : N => a i * F (((x : Whole)*sc T)*u i))
    simp_rw [mul_assoc]
    exact measurable_const.mul (sourceThetaPositiveTensor_scaled_measurable K S c hc U hζ v _)
  obtain ⟨hi,he⟩ := sourceSLocalQuotientSheetProfile_unfold_shifted_hasSum S hζ ν P A u hP h hT hm
    (sourceKPPositiveQuotientSeries_absoluteMass K S hζ v c hc U a u ha hT)
  refine ⟨hi,he.trans ?_⟩
  apply tsum_congr
  intro i
  unfold sourceSLocalSheetProfile sourceThetaPositiveSheet A
  rw [integral_const_mul]
  rfl

end
end ArtinMatthews.SourceReflection
