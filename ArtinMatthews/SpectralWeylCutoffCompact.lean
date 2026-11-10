module

public import ArtinMatthews.SpectralWeylHeightCutoff
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

/-! The same exhausting multiplier gives literal compact positive-height
physical tests, including for functions smooth only on positive heights. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace ArtinMatthews

theorem spectralHeightAnnularPartial_zero_low (K : ℕ) {y : ℝ}
    (hy : y ≤ ((2 : ℝ)^(K+1))⁻¹) : spectralHeightAnnularPartial K y = 0 := by
  let c := (2 : ℝ)^(K+1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc₁ : 1 ≤ c := one_le_pow₀ (by norm_num)
  have hInv : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc₁
  have h₁ : c*y ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hy hc.le
    change c*y ≤ c*c⁻¹ at hh
    simpa only [mul_inv_cancel₀ hc.ne'] using hh
  have h₂ : y/c ≤ 1 := (div_le_one hc).mpr (hy.trans (hInv.trans hc₁))
  rw [spectralHeightAnnularPartial_eq,spectralHeightCutStep_zero h₁,spectralHeightCutStep_zero h₂,sub_self]

theorem spectralHeightAnnularPartial_zero_high (K : ℕ) {y : ℝ}
    (hy : 2*(2 : ℝ)^(K+1) ≤ y) : spectralHeightAnnularPartial K y = 0 := by
  let c := (2 : ℝ)^(K+1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc₁ : 1 ≤ c := one_le_pow₀ (by norm_num)
  have hy₀ : 0 ≤ y := (by positivity : 0 ≤ 2*c).trans hy
  have h₁ : 2 ≤ c*y := by
    calc
      2 ≤ 2*c := by nlinarith
      _ ≤ y := hy
      _ ≤ c*y := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc₁ hy₀
  have h₂ : 2 ≤ y/c := (le_div_iff₀ hc).mpr hy
  rw [spectralHeightAnnularPartial_eq,spectralHeightCutStep_one h₁,spectralHeightCutStep_one h₂,sub_self]

theorem spectralWeylProfileCutoff_tsupport {a : ℝ} (ha : 0 < a) (K : ℕ) (f : ℝ → ℂ) :
    tsupport (spectralWeylProfileCutoff a K f) ⊆
      Icc ((a*(2 : ℝ)^(K+1))⁻¹) (2*(2 : ℝ)^(K+1)/a) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra! h
    apply hx
    have hlow : a*x ≤ ((2 : ℝ)^(K+1))⁻¹ := by
      have hh := mul_le_mul_of_nonneg_left h.le ha.le
      convert hh using 1
      field_simp [ha.ne']
    rw [spectralWeylProfileCutoff,spectralHeightAnnularPartial_zero_low K hlow,Complex.ofReal_zero,zero_mul]
  · by_contra! h
    apply hx
    have hhigh : 2*(2 : ℝ)^(K+1) ≤ a*x := by
      have hh := (div_le_iff₀ ha).mp h.le
      simpa only [mul_comm x a] using hh
    rw [spectralWeylProfileCutoff,spectralHeightAnnularPartial_zero_high K hhigh,Complex.ofReal_zero,zero_mul]

theorem spectralWeylProfileCutoff_continuous {a : ℝ} (ha : 0 < a) (K : ℕ) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Ioi (0 : ℝ))) : Continuous (spectralWeylProfileCutoff a K f) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : 0 < x
  · exact ((Complex.continuous_ofReal.comp ((spectralHeightAnnularPartial_continuous K).comp
      (by fun_prop))).continuousAt).mul ((hf x hx).continuousAt (Ioi_mem_nhds hx))
  · have hd : 0 < (a*(2 : ℝ)^(K+1))⁻¹ := by positivity
    apply (continuousAt_const (y := (0 : ℂ))).congr
    filter_upwards [Iio_mem_nhds ((le_of_not_gt hx).trans_lt hd)] with y hy
    have hnot : y ∉ tsupport (spectralWeylProfileCutoff a K f) := by
      intro hmem
      exact (not_le_of_gt hy) ((spectralWeylProfileCutoff_tsupport ha K f hmem).1)
    exact (image_eq_zero_of_notMem_tsupport hnot).symm

theorem spectralWeylProfileCutoff_compact {a : ℝ} (ha : 0 < a) (K : ℕ) (f : ℝ → ℂ) :
    HasCompactSupport (spectralWeylProfileCutoff a K f) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (spectralWeylProfileCutoff_tsupport ha K f)

theorem spectralWeylProfileCutoff_positive {a : ℝ} (ha : 0 < a) (K : ℕ) (f : ℝ → ℂ) :
    tsupport (spectralWeylProfileCutoff a K f) ⊆ Ioi (0 : ℝ) :=
  fun _ hx => (by positivity : 0 < (a*(2 : ℝ)^(K+1))⁻¹).trans_le
    ((spectralWeylProfileCutoff_tsupport ha K f hx).1)

end ArtinMatthews
