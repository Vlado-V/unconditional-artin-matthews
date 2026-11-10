module

public import ArtinMatthews.SourceKPTameJacquetIntegralCore
public import ArtinMatthews.SourceJacquetShellAmplitude
public import ArtinMatthews.SourceJacquetHaarDilation
public import ArtinMatthews.SourceKPTameJacquetShellPoint
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine shell of the induced spherical Jacquet integral.
The pointwise Bruhat formula gives a continuous representative on
the compact shell. Dilation then supplies its exact volume factor. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceLocalValuation K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "shell₀" => sourceJacquetValuationShell K P.val
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)

theorem sourceKPTameJacquetScaledIntegrand_on_shell_image (e l : ℕ) (u : L) (hu : u ∈ shell₀ 0) :
    sourceKPTameJacquetScaledIntegrand K hζ S₀ P e (((π₀ ^ (-(l : ℤ)) : Lˣ) : L) * u) =
      (sourceJacquetScale Q₀ (((e : ℝ) - 2 * (l : ℝ)) / 3) *
        sourceKPTameJacquetShellAmplitude K hζ S₀ P e l u) •
        sourceJacquetBasis ((2 * (l : ℤ) - (e : ℤ) : ℤ) : ZMod 3) := by
  have hν : ν₀ u = 1 := by
    have h := (sourceJacquetValuationShell_mem K P.val 0 u).mp hu
    rwa [WithZero.exp_zero] at h
  have hu₀ : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hν
    exact zero_ne_one hν
  let v := Units.mk0 u hu₀
  have hpoint := sourceKPTameJacquetPoint_scaled_shell K hζ S₀ P (e : ℤ) l v hν
  change sourceKPTameJacquetPoint K hζ S₀ P (e : ℤ) ((π₀ : L) ^ (e : ℤ) * ((π₀ : L) ^ (-(l : ℤ)) * u)) = _ at hpoint
  have hv : (v : L) = u := rfl
  rw [hv] at hpoint
  have hx : (π₀ : L) ^ (e : ℤ) * ((π₀ : L) ^ (-(l : ℤ)) * u) =
      (π₀ : L) ^ ((e : ℤ) - (l : ℤ)) * u := by
    rw [← mul_assoc, ← zpow_add₀ (Units.ne_zero π₀), ← sub_eq_add_neg]
  rw [sourceKPTameJacquetScaledIntegrand, sourceKPTameJacquetIntegrand, Units.val_zpow_eq_zpow_val,
    hpoint, hx, sourceKPTameJacquetShellAmplitude, smul_smul]
  simp only [Int.cast_natCast]
  congr 1
  ring

theorem sourceKPTameJacquetScaledIntegral_shell (hP : P.val ∉ traceBadPlaces K) (e l : ℕ) :
    IntegrableOn (sourceKPTameJacquetScaledIntegrand K hζ S₀ P e) (shell₀ (l : ℤ)) μ₀ ∧
      (∫ H in shell₀ (l : ℤ), sourceKPTameJacquetScaledIntegrand K hζ S₀ P e H ∂μ₀) =
        (sourceJacquetScale Q₀ (((e : ℝ) + (l : ℝ)) / 3) *
          sourceJacquetActualShell K hζ S₀ P e l) •
          sourceJacquetBasis ((2 * (l : ℤ) - (e : ℤ) : ℤ) : ZMod 3) := by
  let t := π₀ ^ (-(l : ℤ))
  let f := sourceKPTameJacquetScaledIntegrand K hζ S₀ P e
  let A := sourceKPTameJacquetShellAmplitude K hζ S₀ P e l
  let z := sourceJacquetScale Q₀ (((e : ℝ) - 2 * (l : ℝ)) / 3)
  let b := sourceJacquetBasis ((2 * (l : ℤ) - (e : ℤ) : ℤ) : ZMod 3)
  let : Measure.IsAddHaarMeasure μ₀ := sourceJacquetHaar_isAddHaar K P.val
  have ht : ν₀ (t : L) = WithZero.exp (l : ℤ) := by
    dsimp only [t]
    rw [Units.val_zpow_eq_zpow_val, sourceJacquetFrequency_valuation K P.val _ hπ₀, neg_neg]
  have hImage := sourceJacquetValuationShell_mul_image K P.val 0 (l : ℤ) t ht
  rw [zero_add] at hImage
  have hpt : Set.EqOn (fun u => f ((t : L) * u)) (fun u => (z * A u) • b) (shell₀ 0) :=
    fun u hu => sourceKPTameJacquetScaledIntegrand_on_shell_image K hζ S₀ P e l u hu
  let g : L → ZMod 3 → ℂ := fun x => (z * A ((t : L)⁻¹ * x)) • b
  have hg : Continuous g := (continuous_const.mul
    ((sourceKPTameJacquetShellAmplitude_continuous K hζ S₀ P e l).comp (continuous_const.mul continuous_id))).smul
      continuous_const
  have he : Set.EqOn g f (shell₀ (l : ℤ)) := by
    intro x hx
    rw [← hImage] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    change (z * A ((t : L)⁻¹ * ((t : L) * u))) • b = f ((t : L) * u)
    rw [← mul_assoc, inv_mul_cancel₀ t.ne_zero, one_mul]
    exact (hpt hu).symm
  have hShell := sourceJacquetValuationShell_isCompact K P.val (l : ℤ)
  refine ⟨(hg.continuousOn.integrableOn_compact (μ := μ₀) hShell).congr_fun he hShell.measurableSet, ?_⟩
  have hShell₀ := sourceJacquetValuationShell_isCompact K P.val 0
  change (∫ H in shell₀ (l : ℤ), f H ∂μ₀) = _
  rw [← hImage, sourceJacquetSetIntegral_dilation K P.val hP t _ f,
    setIntegral_congr_fun hShell₀.measurableSet hpt, integral_smul_const, integral_const_mul]
  have hA : (∫ u in shell₀ 0, A u ∂μ₀) = sourceJacquetActualShell K hζ S₀ P e l :=
    sourceKPTameJacquetShellAmplitude_integral K hζ S₀ P e l
  rw [hA, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  change (‖(t : L)‖ : ℂ) • ((z * sourceJacquetActualShell K hζ S₀ P e l) • b) = _
  rw [sourceJacquetDilation_norm K P.val (l : ℤ) t ht, smul_smul]
  dsimp only [z]
  rw [← mul_assoc, ← sourceJacquetScale_add (sourceJacquetPrimeNorm_pos K S₀ P)]
  rw [show ((↑(l : ℤ) : ℝ) + ((e : ℝ) - 2 * (l : ℝ)) / 3) = ((e : ℝ) + (l : ℝ)) / 3 by push_cast; ring]

end
end ArtinMatthews
