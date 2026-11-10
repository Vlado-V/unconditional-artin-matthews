module

public import ArtinMatthews.SpectralKLInverseIEnvelope
public import ArtinMatthews.SpectralKLWindowDataRapid
public import ArtinMatthews.SpectralKShiftedPointBound
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace ArtinMatthews
open Set MeasureTheory OAI.CubicEisenstein
open scoped ContDiff
noncomputable section

theorem spectralKLPlancherelWeight_abs_bound (t : ℝ) :
    |spectralKLPlancherelWeight t| ≤ (2 / Real.pi ^ 2) * |t| * Real.exp (Real.pi * |t|) := by
  have hs : |Real.sinh (Real.pi * t)| ≤ Real.exp (Real.pi * |t|) := by
    rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos, Real.sinh_eq]
    nlinarith [Real.exp_pos (Real.pi * |t|), Real.exp_pos (-(Real.pi * |t|))]
  rw [spectralKLPlancherelWeight, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 / Real.pi ^ 2)]
  exact mul_le_mul_of_nonneg_left hs (by positivity)

theorem spectralKLInverseKEnvelope_scalar (k : ℕ) (t x E C F a b w : ℝ)
    (hx : 0 < x) (hE : 0 < E) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w)
    (hka : E * a ≤ C * (1 + |t|) ^ k / x ^ k)
    (hfb : (1 + t ^ 2) ^ (k + 2) * E * b ≤ F)
    (hww : w ≤ (2 / Real.pi ^ 2) * |t| * E ^ 2) :
    a * b * w ≤ ((2 / Real.pi ^ 2) * C * F * 2 ^ k) / x ^ k / (1 + t ^ 2) := by
  have hu : 0 < 1 + t ^ 2 := by positivity
  have hpow : (1 + |t|) ^ k ≤ (2 * (1 + t ^ 2)) ^ k := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  have ht : |t| ≤ 1 + t ^ 2 := by nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  have hpa : a ≤ (C * (1 + |t|) ^ k / x ^ k) / E := (le_div_iff₀ hE).mpr (by nlinarith [hka])
  have hpb : b ≤ F / ((1 + t ^ 2) ^ (k + 2) * E) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hfb)
  calc
    _ ≤ ((C * (1 + |t|) ^ k / x ^ k) / E) *
        (F / ((1 + t ^ 2) ^ (k + 2) * E)) * ((2 / Real.pi ^ 2) * |t| * E ^ 2) := by gcongr
    _ ≤ ((C * (2 * (1 + t ^ 2)) ^ k / x ^ k) / E) *
        (F / ((1 + t ^ 2) ^ (k + 2) * E)) * ((2 / Real.pi ^ 2) * (1 + t ^ 2) * E ^ 2) := by gcongr
    _ = _ := by
      rw [mul_pow, pow_add]
      field_simp

theorem spectralKLWindowSynthesis_kernel_bound (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (H : ℝ) (hH : 0 ≤ H) (hh : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ H * (1 + t ^ 2))
    (k : ℕ) (hk : 1 < k) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t : ℝ, a ≤ x →
      ‖schlafliBesselK ((t : ℂ) * Complex.I) x * spectralKLWindowData h g t *
          (spectralKLPlancherelWeight t : ℂ)‖ ≤ C / x ^ k / (1 + t ^ 2) := by
  obtain ⟨CK, hCK, hK⟩ := schlafliBesselK_closed_strip_polynomial_bound k 0 a
    le_rfl (by
      have hr : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 2 ≤ k by omega)
      linarith) ha
  obtain ⟨CF, hCF, hF⟩ := spectralKLWindowData_rapid h g hg hc hp H hH hh (k + 2)
  refine ⟨(2 / Real.pi ^ 2) * CK * CF * 2 ^ k, by positivity, ?_⟩
  intro x t hax
  have hK' := hK 0 t x (by norm_num) hax
  simp only [Complex.ofReal_zero, zero_add] at hK'
  have he : (Real.exp (Real.pi * |t| / 2)) ^ 2 = Real.exp (Real.pi * |t|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hb := spectralKLInverseKEnvelope_scalar k t x (Real.exp (Real.pi * |t| / 2)) CK CF
    ‖schlafliBesselK ((t : ℂ) * Complex.I) x‖ ‖spectralKLWindowData h g t‖ |spectralKLPlancherelWeight t|
    (ha.trans_le hax) (Real.exp_pos _) hCK.le hCF (norm_nonneg _) (norm_nonneg _) (abs_nonneg _)
    hK' (hF t) (by rw [he]; exact spectralKLPlancherelWeight_abs_bound t)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using hb

end
end ArtinMatthews
