module

public import ArtinMatthews.SpectralKLDirectDefinitions
public import ArtinMatthews.SpectralKLInverseKEnvelope
public import ArtinMatthews.SpectralKShiftedPointBound
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

namespace ArtinMatthews
open Set MeasureTheory OAI.CubicEisenstein
noncomputable section

theorem spectralKLDirectSynthesis_kernel_bound (F : ℝ → ℂ)
    (hrapid : SpectralKLDirectRapid F)
    (k : ℕ) (hk : 1 < k) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t : ℝ, a ≤ x →
      ‖schlafliBesselK ((t : ℂ) * Complex.I) x * F t *
          (spectralKLPlancherelWeight t : ℂ)‖ ≤ C / x ^ k / (1 + t ^ 2) := by
  obtain ⟨CK, hCK, hK⟩ := schlafliBesselK_closed_strip_polynomial_bound k 0 a
    le_rfl (by
      have hr : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 2 ≤ k by omega)
      linarith) ha
  obtain ⟨CF, hCF, hF⟩ := hrapid (k + 2)
  refine ⟨(2 / Real.pi ^ 2) * CK * CF * 2 ^ k, by positivity, ?_⟩
  intro x t hax
  have hK' := hK 0 t x (by norm_num) hax
  simp only [Complex.ofReal_zero, zero_add] at hK'
  have he : (Real.exp (Real.pi * |t| / 2)) ^ 2 = Real.exp (Real.pi * |t|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hb := spectralKLInverseKEnvelope_scalar k t x (Real.exp (Real.pi * |t| / 2)) CK CF
    ‖schlafliBesselK ((t : ℂ) * Complex.I) x‖ ‖F t‖ |spectralKLPlancherelWeight t|
    (ha.trans_le hax) (Real.exp_pos _) hCK.le hCF (norm_nonneg _) (norm_nonneg _) (abs_nonneg _)
    hK' (hF t) (by rw [he]; exact spectralKLPlancherelWeight_abs_bound t)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using hb


end
end ArtinMatthews
