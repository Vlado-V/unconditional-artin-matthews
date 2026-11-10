module

public import ArtinMatthews.SLocalNormOneUnfold
public import ArtinMatthews.SourceSLocalQuotientReflection
public import ArtinMatthews.SourceThetaProfileSmoothing
public import ArtinMatthews.SourceSLocalQuotientSheet
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Tensor periodization on a norm sheet commutes with the quotient
reflection by reindexing the distinct sixth powers by inversion. -/
namespace ArtinMatthews.SourcePhysical
open NumberField IsDedekindDomain MeasureTheory SourceReflection
open scoped NumberField Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "N" => SNormOne K S
local notation "Q" => SNormOneSixthQuotient K S
local notation "U" => SWholeUnits K S
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "qmk" => sNormOneSixthQuotientMap K S

theorem sNormOnePeriodize_mk_group (f : N → ℂ) (n : N) :
    sNormOnePeriodize K S f (qmk n) = ∑' γ : Γ, f (n * γ.val) := by
  rw [sNormOnePeriodize_mk]
  exact ((Subgroup.equivOp Γ).tsum_eq (fun γ : (Γ).op => f (γ • n))).symm

def sourceSLocalTensorOrbit (F : U → ℂ) (u : U) : Q → ℂ :=
  sNormOnePeriodize K S (fun n : N => F ((n : U) * u))

theorem sourceSLocalTensorOrbit_mk (F : U → ℂ) (u : U) (n : N) :
    sourceSLocalTensorOrbit S F u (qmk n) =
      ∑' γ : Γ, F (((n * γ.val : N) : U) * u) :=
  sNormOnePeriodize_mk_group S _ n

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "sc" => sLocalPositiveScaling K hζ S

private theorem reflection_orbit_point (a : U) {T : ℝ} (hT : 0 < T) (n : N) (γ : Γ) :
    a * ((((n * γ.val : N) : U) * sc T))⁻¹ =
      (((sourceSLocalReflectionRatio S hζ a hT * n⁻¹) * (γ⁻¹ : Γ).val : N) : U) *
        sc (sLocalNorm K S a / T) := by
  rw [sourceSLocalReflectionRatio_lift S hζ a hT, mul_inv_rev]
  change (((sourceSLocalReflectionRatio S hζ a hT * (γ.val⁻¹ * n⁻¹) : N) : U) * _) =
    (((sourceSLocalReflectionRatio S hζ a hT * n⁻¹ * γ.val⁻¹ : N) : U) * _)
  congr 2
  ac_rfl

theorem sourceSLocalTensorOrbit_reflection_absSummable_iff (F : U → ℂ)
    (a : U) {T : ℝ} (hT : 0 < T) (n : N) :
    Summable (fun γ : Γ => ‖F (a * (((n * γ.val : N) : U) * sc T)⁻¹)‖) ↔
      Summable (fun γ : Γ =>
        ‖F ((((sourceSLocalReflectionRatio S hζ a hT * n⁻¹) * γ.val : N) : U) *
          sc (sLocalNorm K S a / T))‖) := by
  simp_rw [reflection_orbit_point S hζ a hT]
  exact (Equiv.inv Γ).summable_iff (f := fun γ : Γ =>
    ‖F ((((sourceSLocalReflectionRatio S hζ a hT * n⁻¹) * γ.val : N) : U) *
      sc (sLocalNorm K S a / T))‖)

theorem sourceSLocalTensorOrbit_reflection (F : U → ℂ) (a : U) {T : ℝ}
    (hT : 0 < T) (q : Q) :
    sourceSLocalTensorOrbit S (fun x => F (a * x⁻¹)) (sc T) q =
      sourceSLocalTensorOrbit S F (sc (sLocalNorm K S a / T))
        (sourceSLocalQuotientReflection S hζ a hT q) := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  rw [show (n : Q) = qmk n by rfl, sourceSLocalQuotientReflection_apply_mk,
    sourceSLocalTensorOrbit_mk, sourceSLocalTensorOrbit_mk]
  simp_rw [reflection_orbit_point S hζ a hT]
  exact (Equiv.inv Γ).tsum_eq (fun γ : Γ =>
    F ((((sourceSLocalReflectionRatio S hζ a hT * n⁻¹) * γ.val : N) : U) *
      sc (sLocalNorm K S a / T)))

def sourceSLocalTensorOrbitProfile (ν : Measure N) (F : U → ℂ) (T : ℝ) : ℂ :=
  ∫ q, sourceSLocalTensorOrbit S F (sc T) q ∂sNormOneQuotientMeasure K S ν

variable (ν : Measure (SNormOne K S)) [ν.IsHaarMeasure]

theorem sourceSLocalTensorOrbitProfile_reflection (F : U → ℂ) (a : U) {T : ℝ} (hT : 0 < T) :
    sourceSLocalTensorOrbitProfile S hζ ν (fun x => F (a * x⁻¹)) T =
      sourceSLocalTensorOrbitProfile S hζ ν F (sLocalNorm K S a / T) := by
  unfold sourceSLocalTensorOrbitProfile
  calc
    _ = ∫ q, sourceSLocalTensorOrbit S F (sc (sLocalNorm K S a / T))
        (sourceSLocalQuotientReflection S hζ a hT q) ∂sNormOneQuotientMeasure K S ν :=
      integral_congr_ae (Filter.Eventually.of_forall (sourceSLocalTensorOrbit_reflection S hζ F a hT))
    _ = _ := (sourceSLocalQuotientReflection_measurePreserving S hζ ν a hT).integral_comp' _

theorem sourceSLocalTensorOrbitGaussian_reflection (F : U → ℂ) (a : U)
    (C₀ A₀ : ℝ) (r : ℕ) {u : ℝ} (hu : 0 < u) :
    sourceThetaGaussianProfile C₀ A₀ r 1 (sourceSLocalTensorOrbitProfile S hζ ν (fun x => F (a * x⁻¹))) u =
      sourceThetaGaussianProfile C₀ A₀ r (-1) (sourceSLocalTensorOrbitProfile S hζ ν F)
        (sLocalNorm K S a / u) := by
  have heq (T : ℝ) (hT : 0 < T) :
      sourceSLocalTensorOrbitProfile S hζ ν (fun x => F (a * x⁻¹)) T =
        (1 : ℂ) * sourceSLocalTensorOrbitProfile S hζ ν F (sLocalNorm K S a / T) := by
    rw [one_mul, sourceSLocalTensorOrbitProfile_reflection S hζ ν F a hT]
  simpa only [one_mul] using
    sourceThetaGaussianProfile_reflection_of_pointwise _ _ _ 1 heq C₀ A₀ r hu

end
end ArtinMatthews.SourcePhysical
