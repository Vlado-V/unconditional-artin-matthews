module

public import ArtinMatthews.SourceKPExteriorScattering
public import ArtinMatthews.SourceKPTameIntertwiningIntegral
public import ArtinMatthews.ProbeIdealSourceRegions
public import ArtinMatthews.SourceKPTameIntertwiningLimit
public import ArtinMatthews.StandardLocalHaarScaling
public import ArtinMatthews.VaryingKummerAnalyticRayIdealCoefficients
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
public import Mathlib.Order.CompletePartialOrder
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

/-! Absolute convergence and whole-field evaluation of the parameter-dependent
spherical intertwining integral. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical StandardAdelic
open QuadraticWeil VaryingKummerAnalytic
open scoped NumberField SourcePhysical BigOperators Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceLocalValuation K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P
local notation "shell₀" => sourceJacquetValuationShell K P.val
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "B₀" => sourceLocalBall K P.val

lemma sourceKPTameIntertwiningBasis_norm_le (i : ZMod 3) :
    ‖sourceJacquetBasis i‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro j
  simp only [sourceJacquetBasis, Pi.single_apply]
  split_ifs <;> norm_num

lemma sourceKPTameIntertwiningCharacter_norm_le
    (χ : MulChar ((𝓞 K) ⧸ P.val.asIdeal) ℂ) (x : L) :
    ‖sourceJacquetWeight K P.val χ x‖ ≤ 1 := by
  unfold sourceJacquetWeight
  split_ifs
  · exact finiteMulChar_norm_le_one χ _
  · simp

lemma sourceKPTameIntertwiningIntegrand_norm_shell (s : ℂ) (l : ℕ) (x : L)
    (hx : x ∈ shell₀ (l : ℤ)) :
    ‖sourceKPTameIntertwiningIntegrand K hζ S₀ P s x‖ ≤
      Real.exp (-(2 * s.re + 1) * (l : ℝ) * Real.log Q₀) := by
  let t := π₀ ^ (-(l : ℤ))
  have ht : ν₀ (t : L) = WithZero.exp (l : ℤ) := by
    dsimp only [t]
    rw [Units.val_zpow_eq_zpow_val, sourceJacquetFrequency_valuation K P.val _ hπ₀, neg_neg]
  have hImage := sourceJacquetValuationShell_mul_image K P.val 0 (l : ℤ) t ht
  rw [zero_add] at hImage
  rw [← hImage] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [sourceKPTameIntertwiningIntegrand_on_shell_image K hζ S₀ P s l u hu,
    norm_smul, norm_mul]
  have he : (-(2*s+1) * (l : ℂ) * (Real.log Q₀ : ℂ)).re =
      -(2 * s.re + 1) * (l : ℝ) * Real.log Q₀ := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.one_re, mul_zero, zero_mul, sub_zero]
  rw [Complex.norm_exp, he]
  calc
    _ ≤ Real.exp (-(2 * s.re + 1) * (l : ℝ) * Real.log Q₀) * 1 * 1 := by
      gcongr
      · exact sourceKPTameIntertwiningCharacter_norm_le K S₀ P _ u
      · exact sourceKPTameIntertwiningBasis_norm_le _
    _ = _ := by ring

lemma sourceKPTameIntertwiningShell_volume_le (l : ℕ) :
    (μ₀).real (shell₀ (l : ℤ)) ≤ Q₀ ^ l := by
  let : Measure.IsAddHaarMeasure μ₀ := sourceJacquetHaar_isAddHaar K P.val
  have hzero : (μ₀).real (B₀ 0) = 1 := by
    rw [sourceLocalBall_zero_eq_integerOpen, Measure.real, sourceJacquetHaar_integers,
      ENNReal.toReal_one]
  calc
    (μ₀).real (shell₀ (l : ℤ)) ≤ (μ₀).real (B₀ (l : ℤ)) :=
      measureReal_mono (fun _ hx => hx.1) (sourceLocalBall_isCompact K P.val _).measure_ne_top
    _ = Q₀ ^ l := by rw [sourceLocalBall_volume_scaling K P.val μ₀, hzero, mul_one, zpow_natCast]

lemma sourceKPTameIntertwiningShells_cover :
    B₀ 0 ∪ (⋃ l : ℕ, shell₀ (l : ℤ)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : ν₀ x = 0
  · left
    change ν₀ x ≤ WithZero.exp (0 : ℤ)
    rw [hx]
    exact zero_le
  · let m : ℤ := WithZero.log (ν₀ x)
    have he : ν₀ x = WithZero.exp m := (WithZero.exp_log hx).symm
    by_cases hm : m ≤ 0
    · left
      change ν₀ x ≤ WithZero.exp (0 : ℤ)
      rw [he]
      exact WithZero.exp_le_exp.mpr hm
    · right
      apply Set.mem_iUnion.mpr
      refine ⟨m.toNat, ?_⟩
      rw [sourceJacquetValuationShell_mem, Int.toNat_of_nonneg (by omega : 0 ≤ m)]
      exact he

lemma sourceKPTameIntertwiningBalls_cover :
    (⋃ N : ℕ, B₀ ((3 * N : ℕ) : ℤ)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : ν₀ x = 0
  · exact Set.mem_iUnion.mpr ⟨0, by
      change ν₀ x ≤ WithZero.exp (0 : ℤ)
      rw [hx]
      exact zero_le⟩
  · let m : ℤ := WithZero.log (ν₀ x)
    have he : ν₀ x = WithZero.exp m := (WithZero.exp_log hx).symm
    apply Set.mem_iUnion.mpr
    refine ⟨m.toNat, ?_⟩
    change ν₀ x ≤ WithZero.exp ((3 * m.toNat : ℕ) : ℤ)
    rw [he]
    apply WithZero.exp_le_exp.mpr
    have hm : m ≤ (m.toNat : ℤ) := Int.self_le_toNat m
    omega

lemma sourceKPTameIntertwiningShell_integral_norm_le (s : ℂ) (l : ℕ) :
    (∫ x in shell₀ (l : ℤ), ‖sourceKPTameIntertwiningIntegrand K hζ S₀ P s x‖ ∂μ₀) ≤
      Real.exp (-2 * s.re * (l : ℝ) * Real.log Q₀) := by
  let f := sourceKPTameIntertwiningIntegrand K hζ S₀ P s
  let : Measure.IsAddHaarMeasure μ₀ := sourceJacquetHaar_isAddHaar K P.val
  have hnorm := norm_setIntegral_le_of_norm_le_const
    (μ := μ₀) (f := fun x => ‖f x‖)
    (sourceJacquetValuationShell_isCompact K P.val (l : ℤ)).measure_lt_top
    (fun x hx => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact sourceKPTameIntertwiningIntegrand_norm_shell K hζ S₀ P s l x hx)
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hnorm
  calc
    _ ≤ Real.exp (-(2 * s.re + 1) * (l : ℝ) * Real.log Q₀) * (μ₀).real (shell₀ (l : ℤ)) := hnorm
    _ ≤ Real.exp (-(2 * s.re + 1) * (l : ℝ) * Real.log Q₀) * Q₀ ^ l := by
      exact mul_le_mul_of_nonneg_left (sourceKPTameIntertwiningShell_volume_le K S₀ P l)
        (Real.exp_pos _).le
    _ = Real.exp (-2 * s.re * (l : ℝ) * Real.log Q₀) := by
      have hQ : 0 < Q₀ := sourceJacquetPrimeNorm_pos K S₀ P
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hQ, ← Real.exp_add]
      congr 1
      ring

lemma sourceKPTameIntertwiningShell_integral_norm_summable {s : ℂ} (hs : 0 < s.re) :
    Summable (fun l : ℕ => ∫ x in shell₀ (l : ℤ),
      ‖sourceKPTameIntertwiningIntegrand K hζ S₀ P s x‖ ∂μ₀) := by
  have hlog : 0 < Real.log Q₀ := Real.log_pos (probeIdealPrime_norm_gt_one K P.val)
  have hr : Real.exp (-2 * s.re * Real.log Q₀) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hg := summable_geometric_of_lt_one (Real.exp_pos (-2 * s.re * Real.log Q₀)).le hr
  apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _ hg
  intro l
  convert sourceKPTameIntertwiningShell_integral_norm_le K hζ S₀ P s l using 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem sourceKPTameIntertwiningIntegrand_integrable (hP : P.val ∉ traceBadPlaces K)
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (sourceKPTameIntertwiningIntegrand K hζ S₀ P s) μ₀ := by
  let f := sourceKPTameIntertwiningIntegrand K hζ S₀ P s
  let : Measure.IsAddHaarMeasure μ₀ := sourceJacquetHaar_isAddHaar K P.val
  have hzero : IntegrableOn f (B₀ 0) μ₀ := by
    exact ((continuous_const : Continuous (fun _ : L => sourceJacquetBasis (0 : ZMod 3))).continuousOn.integrableOn_compact
      (μ := μ₀) (sourceLocalBall_isCompact K P.val 0)).congr_fun
        (fun x hx => (sourceKPTameIntertwiningIntegrand_on_zero K hζ S₀ P s x hx).symm)
        (sourceLocalBall_isCompact K P.val 0).measurableSet
  have hshells : IntegrableOn f (⋃ l : ℕ, shell₀ (l : ℤ)) μ₀ :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun l => (sourceKPTameIntertwiningIntegral_shell K hζ S₀ P hP s l).1)
      (sourceKPTameIntertwiningShell_integral_norm_summable K hζ S₀ P hs)
  have h := hzero.union hshells
  rwa [sourceKPTameIntertwiningShells_cover K S₀ P, integrableOn_univ] at h

theorem sourceKPTameIntertwiningTruncation_tendsto_integral (hP : P.val ∉ traceBadPlaces K)
    {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun N : ℕ => sourceKPTameIntertwiningTruncation K hζ S₀ P s (3 * N))
      Filter.atTop (nhds (∫ x, sourceKPTameIntertwiningIntegrand K hζ S₀ P s x ∂μ₀)) := by
  have hmono : Monotone (fun N : ℕ => B₀ ((3 * N : ℕ) : ℤ)) := by
    intro a b hab x hx
    exact (show ν₀ x ≤ WithZero.exp ((3 * a : ℕ) : ℤ) from hx).trans
      (WithZero.exp_le_exp.mpr (by exact_mod_cast Nat.mul_le_mul_left 3 hab))
  have hI : IntegrableOn (sourceKPTameIntertwiningIntegrand K hζ S₀ P s)
      (⋃ N : ℕ, B₀ ((3 * N : ℕ) : ℤ)) μ₀ := by
    rw [sourceKPTameIntertwiningBalls_cover K S₀ P, integrableOn_univ]
    exact sourceKPTameIntertwiningIntegrand_integrable K hζ S₀ P hP hs
  have h := tendsto_setIntegral_of_monotone
    (fun N => (sourceLocalBall_isCompact K P.val ((3 * N : ℕ) : ℤ)).measurableSet) hmono hI
  simpa only [sourceKPTameIntertwiningBalls_cover K S₀ P, setIntegral_univ,
    sourceKPTameIntertwiningTruncation] using h

theorem sourceKPTameIntertwiningIntegral_eq (hP : P.val ∉ traceBadPlaces K)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ x, sourceKPTameIntertwiningIntegrand K hζ S₀ P s x ∂μ₀) =
      sourceKPUnramifiedScatteringFactor P.val s • sourceJacquetBasis 0 :=
  tendsto_nhds_unique
    (sourceKPTameIntertwiningTruncation_tendsto_integral K hζ S₀ P hP hs)
    (sourceKPTameIntertwiningTruncation_tendsto K hζ S₀ P hP hs)

end
end ArtinMatthews
