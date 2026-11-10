module

public import ArtinMatthews.SourceSLocalRadialInvariance
public import ArtinMatthews.SLocalNormOneTopology
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

/-! The affine norm-sheet reflection descends to the actual sixth-power
quotient and preserves its inherited Haar normalization. -/
namespace ArtinMatthews.SourcePhysical
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "N" => SNormOne K S
local notation "Q" => SNormOneSixthQuotient K S
local notation "U" => SWholeUnits K S
local notation "qmk" => sNormOneSixthQuotientMap K S
local notation "sc" => sLocalPositiveScaling K hζ S

private theorem reflectionRatio_norm (a : U) {T : ℝ} (hT : 0 < T) :
    sLocalNorm K S (a * (sc T)⁻¹) = sLocalNorm K S (sc (sLocalNorm K S a / T)) := by
  rw [sLocalNorm_mul, sLocalNorm_inv, sLocalPositiveScaling_norm K hζ S hT,
    sLocalPositiveScaling_norm K hζ S (div_pos (sLocalNorm_pos K S a) hT),
    div_eq_mul_inv]

def sourceSLocalReflectionRatio (a : U) {T : ℝ} (hT : 0 < T) : N :=
  sourceSLocalSameNormRatio S _ _ (reflectionRatio_norm S hζ a hT)

theorem sourceSLocalReflectionRatio_lift (a : U) {T : ℝ} (hT : 0 < T) (n : N) :
    a * ((n : U) * sc T)⁻¹ =
      ((sourceSLocalReflectionRatio S hζ a hT * n⁻¹ : N) : U) * sc (sLocalNorm K S a / T) := by
  let k := sourceSLocalReflectionRatio S hζ a hT
  have hk : (k : U) * sc (sLocalNorm K S a / T) = a * (sc T)⁻¹ :=
    sourceSLocalSameNormRatio_mul S _ _ (reflectionRatio_norm S hζ a hT)
  change a * ((n : U) * sc T)⁻¹ = ((k : U) * (n : U)⁻¹) * sc (sLocalNorm K S a / T)
  rw [mul_inv_rev, mul_comm (k : U) (n : U)⁻¹, mul_assoc, hk]
  ac_rfl

def sourceSLocalQuotientReflection (a : U) {T : ℝ} (hT : 0 < T) : Q ≃ᵐ Q := by
  let : BorelSpace Q := sNormOneSixthQuotient_borel K S
  let : SecondCountableTopology Q := sNormOneSixthQuotient_secondCountable K S
  exact (MeasurableEquiv.inv Q).trans (MeasurableEquiv.mulLeft (qmk (sourceSLocalReflectionRatio S hζ a hT)))

theorem sourceSLocalQuotientReflection_apply_mk (a : U) {T : ℝ} (hT : 0 < T) (n : N) :
    sourceSLocalQuotientReflection S hζ a hT (qmk n) =
      qmk (sourceSLocalReflectionRatio S hζ a hT * n⁻¹) := by
  change qmk (sourceSLocalReflectionRatio S hζ a hT) * (qmk n)⁻¹ = _
  rw [map_mul, map_inv]

theorem sourceSLocalQuotientReflection_measurePreserving
    (ν : Measure N) [ν.IsHaarMeasure] (a : U) {T : ℝ} (hT : 0 < T) :
    MeasurePreserving (sourceSLocalQuotientReflection S hζ a hT)
      (sNormOneQuotientMeasure K S ν) (sNormOneQuotientMeasure K S ν) := by
  let : BorelSpace Q := sNormOneSixthQuotient_borel K S
  let : SecondCountableTopology Q := sNormOneSixthQuotient_secondCountable K S
  let : T2Space Q := sNormOneSixthQuotient_t2 K S
  let : CompactSpace Q := sNormOneSixthQuotient_compact K S
  let μ := sNormOneQuotientMeasure K S ν
  let : IsFiniteMeasure μ := sNormOneQuotientMeasure_finite K S ν
  let : μ.IsHaarMeasure := sNormOneQuotientMeasure_isHaar K S ν
  exact (measurePreserving_mul_left μ (qmk (sourceSLocalReflectionRatio S hζ a hT))).comp
    (Measure.measurePreserving_inv μ)

end
end ArtinMatthews.SourcePhysical
