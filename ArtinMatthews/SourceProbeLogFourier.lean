module

public import ArtinMatthews.SourceProbeLogProfile
public import ArtinMatthews.SourceCompactLogFourier
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

namespace ArtinMatthews.SourcePhysical
open NumberField IsDedekindDomain Set Function
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "A" => SLocalAdditiveCompletionSpace K S

/-- The actual normalized Fourier coefficients of the log-periodic probe. -/
def sourceProbeLogFourierCoeff (y : A) (j : ℤ) : ℂ :=
  sourceLogPeriodCoeff (sourceProbeLogProfile K hζ S y) j

/-- The exact phase in each separated summand. -/
def sourceProbeLogFourierPhase (v : ℝ) (j : ℤ) : ℂ :=
  fourier j (Real.log v : UnitAddCircle)

theorem sourceProbeLogFourierPhase_norm (v : ℝ) (j : ℤ) :
    ‖sourceProbeLogFourierPhase v j‖ = 1 := by
  rw [sourceProbeLogFourierPhase, fourier_apply]
  exact Circle.norm_coe _

theorem sourceProbeLogFourierPhase_exp (v : ℝ) (j : ℤ) :
    sourceProbeLogFourierPhase v j = Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * Real.log v) := by
  rw [sourceProbeLogFourierPhase, fourier_coe_apply, Complex.ofReal_one, div_one]

theorem sourceProbeLogFourierCoeff_eq_zero_outside {y : A}
    (hy : y ∉ sourceProbeEnlargedAnnulus K hζ S) (j : ℤ) :
    sourceProbeLogFourierCoeff K hζ S y j = 0 := by
  rw [sourceProbeLogFourierCoeff, sourceProbeLogProfile_zero_outside_enlarged K hζ S hy]
  simp [sourceLogPeriodCoeff, fourierCoeff, AddCircle.liftIoc]

/-- The cost bound is uniform on the full additive space, with the actual compact support. -/
theorem sourceProbeLogFourierCoeff_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : A) (j : ℤ),
      ‖sourceProbeLogFourierCoeff K hζ S y j‖ ≤ C * sourceLogFrequencyDecay j := by
  obtain ⟨C, hC, hB⟩ := sourceProbeLogProfile_uniform_bound K hζ S
  refine ⟨C, hC, fun y j => ?_⟩
  exact sourceLogPeriodCoeff_bound (sourceProbeLogProfile_contDiff K hζ S y)
    ((sourceProbeLogProfile_tsupport K hζ S y).trans sourceProbeLogSupport_subset_period)
    (fun t ht => (hB y t ht).1) (fun t ht => (hB y t ht).2) j

/-- The actual supremum norm of each coefficient, taken over all completion variables. -/
def sourceProbeLogFourierCost (j : ℤ) : ℝ :=
  ⨆ y : A, ‖sourceProbeLogFourierCoeff K hζ S y j‖

theorem sourceProbeLogFourierCoeff_norm_le_cost (y : A) (j : ℤ) :
    ‖sourceProbeLogFourierCoeff K hζ S y j‖ ≤ sourceProbeLogFourierCost K hζ S j := by
  obtain ⟨C, _, hC⟩ := sourceProbeLogFourierCoeff_uniform_bound K hζ S
  exact le_ciSup ⟨C * sourceLogFrequencyDecay j, fun _ ⟨z, hz⟩ => hz ▸ hC z j⟩ y

theorem sourceProbeLogFourierCost_nonneg (j : ℤ) : 0 ≤ sourceProbeLogFourierCost K hζ S j :=
  (norm_nonneg _).trans (sourceProbeLogFourierCoeff_norm_le_cost K hζ S 0 j)

theorem sourceProbeLogFourierCost_summable : Summable (sourceProbeLogFourierCost K hζ S) := by
  obtain ⟨C, _, hC⟩ := sourceProbeLogFourierCoeff_uniform_bound K hζ S
  have hsum : Summable (fun j => C * sourceLogFrequencyDecay j) :=
    sourceLogFrequencyDecay_summable.mul_left C
  exact Summable.of_nonneg_of_le (sourceProbeLogFourierCost_nonneg K hζ S)
    (fun j => ciSup_le (fun y => hC y j)) hsum

theorem sourceProbeLogFourierCoeff_summable_norm (y : A) :
    Summable (fun j => ‖sourceProbeLogFourierCoeff K hζ S y j‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (sourceProbeLogFourierCoeff_norm_le_cost K hζ S y)
    (sourceProbeLogFourierCost_summable K hζ S)

theorem sourceProbeLogProfile_at_log (y : A) {v : ℝ} (hv : 0 < v) :
    sourceProbeLogProfile K hζ S y (Real.log v) =
      (Real.sqrt v : ℂ)⁻¹ * sourceProbeW1Complex v *
        sourceSLocalCompletionProbe K S
          (y * sourceSLocalUnitAdditivePoint K S (sLocalPositiveScaling K hζ S v)⁻¹) := by
  rw [sourceProbeLogProfile, sourceProbeLogDilate_neg, Real.exp_log hv, neg_div,
    Real.exp_neg, Complex.ofReal_inv, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hv]
  rw [show Real.log v / 2 = Real.log v * (1 / 2) by ring]

/-- Fourier separation on the entire actual support of `W₁`, with normalized Haar coefficients. -/
theorem sourceProbeLogFourier_hasSum (y : A) {v : ℝ} (hv : v ∈ Icc (3 / 2 : ℝ) (5 / 2)) :
    HasSum (fun j => sourceProbeLogFourierCoeff K hζ S y j * sourceProbeLogFourierPhase v j)
      ((Real.sqrt v : ℂ)⁻¹ * sourceProbeW1Complex v *
        sourceSLocalCompletionProbe K S
          (y * sourceSLocalUnitAdditivePoint K S (sLocalPositiveScaling K hζ S v)⁻¹)) := by
  have hpos : 0 < v := (by norm_num : (0 : ℝ) < 3 / 2).trans_le hv.1
  have hlog : Real.log v ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self
    (sourceProbeLogSupport_subset_period ⟨Real.log_le_log (by norm_num) hv.1,
      Real.log_le_log hpos hv.2⟩)
  rw [← sourceProbeLogProfile_at_log K hζ S y hpos]
  exact sourceLogPeriodCoeff_hasSum (sourceProbeLogProfile_contDiff K hζ S y).continuous
    ((sourceProbeLogProfile_tsupport K hζ S y).trans sourceProbeLogSupport_subset_period)
    (sourceProbeLogFourierCoeff_summable_norm K hζ S y).of_norm hlog

end
end ArtinMatthews.SourcePhysical
