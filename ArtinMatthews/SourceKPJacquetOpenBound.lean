module

public import ArtinMatthews.SourceKPJacquetShellBound
public import ArtinMatthews.SourceKPJacquetFlatDiagonal
public import ArtinMatthews.ProbeIdealSourceRegions
public import ArtinMatthews.SourceKPJacquetOuterShift
public import ArtinMatthews.StandardLocalBallDilation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual open-cell value at the negative parameter has the
power envelope used in the finite Jacquet shell estimate. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical MeasureTheory
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "B" => sourceLocalBall K P
local notation "Q" => (Ideal.absNorm P.asIdeal : ℝ)
local notation "ν₀" => sourceLocalValuation K P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "n₀" => fun t : L => l₀ (sourceGL2Upper t)
local notation "n₋" => fun t : L => l₀ (sourceGL2Lower t)
local notation "d₀" => sourceFiniteKPProjectiveBorelDiagonal K hζ P
local notation "w₀" => l₀ sourceGL2Weyl
local notation "μ₀" => sourceLocalSelfDual K P
local notation "F" => sourceKPJacquetOpenEnvelope K P

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)
    {ι : Type*} [Fintype ι] (e : V ≃ₗ[ℂ] (ι → ℂ))
local notation "I₀" => sourceAlgebraicInducedSpace B₀ ρ
local notation "E" => sourceKPJacquetFrequencyIntegrand K hζ P ρ e
local notation "D" => sourceKPJacquetFlatDiagonal K hζ P ρ

theorem sourceKPJacquet_open_value_bound
    (hUpper : ∀ t : L, ∀ v : V, ρ (sourceFiniteKPProjectiveBorelUpper K hζ P t) v = v)
    (hCube : SourceKPJacquetNegativeCubeLaw K hζ P ρ) (f : I₀) (N : ℕ)
    (hFix : ∀ t ∈ B (-(N : ℤ)), ∀ g : G,
      f.val (g * n₀ t) = f.val g ∧ f.val (g * n₋ t) = f.val g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : L, ‖e (f.val (w₀ * n₀ x))‖ ≤ C * F x := by
  obtain ⟨A, hA, hD⟩ := sourceKPJacquetFlatDiagonal_norm_bound K hζ P ρ e hCube
  have hcont : Continuous (E 1 f) := sourceKPJacquetFrequencyIntegrand_continuous K hζ P ρ e 1 f N
    (fun t ht g => (hFix t ht g).1)
  obtain ⟨C₀, hC₀⟩ := (sourceLocalBall_isCompact K P (N : ℤ)).exists_bound_of_continuousOn hcont.continuousOn
  let Y : ℝ := Q ^ N
  let L₀ := max 1 C₀ * Y ^ (2 / 3 : ℝ)
  let L₁ := A * ‖e (f.val 1)‖
  have hQ : 1 < Q := VaryingKummerAnalytic.probeIdealPrime_norm_gt_one K P
  have hY : 1 ≤ Y := one_le_pow₀ hQ.le
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hL₀ : 0 < L₀ := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (Real.rpow_pos_of_pos hY0 _)
  have hL₁ : 0 ≤ L₁ := mul_nonneg hA.le (norm_nonneg _)
  have hF (x : L) : 0 < F x := Real.rpow_pos_of_pos (zero_lt_one.trans_le (le_max_left _ _)) _
  refine ⟨L₀ + L₁, add_pos_of_pos_of_nonneg hL₀ hL₁, fun x => ?_⟩
  by_cases hx : x ∈ B (N : ℤ)
  · have hxN : ‖x‖ ≤ Y := by
      simpa only [zpow_natCast] using sourceKPJacquet_norm_le_of_ball K P hx
    have hp : Y ^ (-(2 / 3) : ℝ) ≤ F x := by
      exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le (le_max_left _ _))
        (max_le hY hxN) (by norm_num)
    have hm : 1 ≤ Y ^ (2 / 3 : ℝ) * F x := by
      calc
        1 = Y ^ (2 / 3 : ℝ) * Y ^ (-(2 / 3) : ℝ) := by
          rw [← Real.rpow_add hY0, add_neg_cancel, Real.rpow_zero]
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hY0.le _)
    calc
      _ = ‖E 1 f x‖ := (sourceKPJacquetFrequencyIntegrand_norm K hζ P ρ e 1 f x).symm
      _ ≤ C₀ := hC₀ x hx
      _ ≤ max 1 C₀ * (Y ^ (2 / 3 : ℝ) * F x) :=
        (le_max_right _ _).trans (le_mul_of_one_le_right (zero_le_one.trans (le_max_left _ _)) hm)
      _ = L₀ * F x := by dsimp only [L₀]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hL₁) (hF x).le
  · have hν : WithZero.exp (N : ℤ) < ν₀ x := lt_of_not_ge hx
    have hν0 : 0 < ν₀ x := zero_le.trans_lt hν
    have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).mp hν0.ne'
    have hlog : (N : ℤ) < WithZero.log (ν₀ x) := by
      apply WithZero.exp_lt_exp.mp
      rwa [WithZero.exp_log hν0.ne']
    have hinv : x⁻¹ ∈ B (-(N : ℤ)) := by
      change ν₀ x⁻¹ ≤ WithZero.exp (-(N : ℤ))
      rw [map_inv₀, ← WithZero.exp_log hν0.ne', ← WithZero.exp_neg, WithZero.exp_le_exp]
      omega
    have hxNorm : 1 < ‖x‖ := by
      rw [sourceLocalNorm_eq_zpow K P x hx0, one_lt_zpow_iff_right₀ hQ]
      omega
    let u : Lˣ := Units.mk0 x hx0
    let d := sourceBruhatDiagonal u
    have he : f.val (w₀ * n₀ x) = ρ (d₀ d) (f.val 1) :=
      sourceKPJacquet_open_cell_eval_of_lower_fixed K hζ P ρ f hUpper u (by
        change f.val (n₋ x⁻¹) = f.val 1
        simpa only [one_mul] using (hFix x⁻¹ hinv 1).2)
    have hdn : ‖(d : L)‖ = ‖x‖ ^ (-2 : ℤ) := by
      change ‖-(x⁻¹ ^ (2 : ℕ))‖ = _
      rw [norm_neg, norm_pow, norm_inv, zpow_neg, zpow_ofNat, inv_pow]
    have hd : ‖(d : L)‖ ^ (1 / 3 : ℝ) = F x := by
      rw [hdn, ← Real.rpow_intCast, ← Real.rpow_mul (norm_nonneg x), sourceKPJacquetOpenEnvelope,
        max_eq_right hxNorm.le]
      norm_num
    calc
      _ = F x * ‖e (D d (f.val 1))‖ := by
        rw [he, sourceKPJacquet_diagonal_eq_smul_flat K hζ P ρ, map_smul, norm_smul, Complex.norm_real,
          Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), hd]
      _ ≤ F x * (A * ‖e (f.val 1)‖) := mul_le_mul_of_nonneg_left (hD d _) (hF x).le
      _ = L₁ * F x := by dsimp only [L₁]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hL₀.le) (hF x).le

theorem sourceKPJacquet_frequency_truncation_bound
    (hUpper : ∀ t : L, ∀ v : V, ρ (sourceFiniteKPProjectiveBorelUpper K hζ P t) v = v)
    (hCube : SourceKPJacquetNegativeCubeLaw K hζ P ρ) (f : I₀) (N : ℕ)
    (hFix : ∀ t ∈ B (-(N : ℤ)), ∀ g : G,
      f.val (g * n₀ t) = f.val g ∧ f.val (g * n₋ t) = f.val g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Lˣ) (R : ℕ),
      ‖e (sourceKPJacquetFrequencyTruncation K hζ P ρ e z (R : ℤ) f)‖ ≤ C * (Q ^ (1 / 3 : ℝ)) ^ R := by
  obtain ⟨A, hA, hF⟩ := sourceKPJacquet_open_value_bound K hζ P ρ e hUpper hCube f N hFix
  obtain ⟨C, hC, hS⟩ := sourceKPJacquetOpenEnvelope_ball_bound K P
  refine ⟨A * C, mul_pos hA hC, fun z R => ?_⟩
  have hi := sourceKPJacquetFrequencyIntegrand_integrableOn K hζ P ρ e z f N
    (fun t ht g => (hFix t ht g).1) (R : ℤ)
  let : (μ₀).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  have hf : IntegrableOn (fun x => A * F x) (B (R : ℤ)) μ₀ :=
    (continuous_const.mul (sourceKPJacquetOpenEnvelope_continuous K P)).continuousOn.integrableOn_compact
      (sourceLocalBall_isCompact K P _)
  rw [sourceKPJacquetFrequencyTruncation, e.apply_symm_apply]
  calc
    _ ≤ ∫ x in B (R : ℤ), ‖E z f x‖ ∂μ₀ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in B (R : ℤ), A * F x ∂μ₀ := by
      apply setIntegral_mono_on hi.norm hf (sourceLocalBall_isOpen K P _).measurableSet
      intro x _
      rw [sourceKPJacquetFrequencyIntegrand_norm K hζ P ρ e]
      exact hF x
    _ = A * ∫ x in B (R : ℤ), F x ∂μ₀ := integral_const_mul _ _
    _ ≤ A * (C * (Q ^ (1 / 3 : ℝ)) ^ R) := mul_le_mul_of_nonneg_left (hS R) hA.le
    _ = _ := by ring

end
end ArtinMatthews
