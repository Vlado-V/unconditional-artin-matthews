module

public import ArtinMatthews.SourceLocalMellinShells
public import ArtinMatthews.StandardLocalBallFourier
public import ArtinMatthews.StandardLocalHaarScaling
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Summation of the genuine valuation shells. Both the complex
Mellin integral and its absolute integral are evaluated. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory Set
open scoped NumberField
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

local notation "q" => (Ideal.absNorm P.asIdeal : ℝ)
local notation "μ" => sourceLocalMulMeasure K P

theorem sourceLocalMellinWeight_integrable_ball (n : ℤ) (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (sourceLocalMellinWeight K P z) (sourceLocalMulBall K P n) μ := by
  rw [sourceLocalMulBall_iUnion]
  refine integrableOn_iUnion_of_summable_integral_norm
    (fun m => sourceLocalMellinWeight_integrable_shell K P (n - (m : ℤ)) z) ?_
  simp_rw [sourceLocalMellinWeight_norm_integral_shell]
  exact (hasSum_geometric_of_lt_one (norm_nonneg _)
    (sourceLocalMellinRatio_norm_lt_one K P z hz)).summable.mul_left _

theorem sourceLocalMellinWeight_integral_ball (n : ℤ) (z : ℂ) (hz : 0 < z.re) :
    (∫ u in sourceLocalMulBall K P n, sourceLocalMellinWeight K P z u ∂μ) =
      (sourceLocalMellinShellMass K P : ℂ) * (q : ℂ) ^ ((n : ℂ) * z) /
        (1 - (q : ℂ) ^ (-z)) := by
  have hi := sourceLocalMellinWeight_integrable_ball K P n z hz
  rw [sourceLocalMulBall_iUnion] at hi ⊢
  rw [integral_iUnion (fun m : ℕ => sourceLocalMulShell_measurable K P (n - (m : ℤ)))
    (sourceLocalMulBall_shells_disjoint K P n) hi]
  simp_rw [sourceLocalMellinWeight_integral_shell]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (sourceLocalMellinRatio_norm_lt_one K P z hz),
    div_eq_mul_inv]

theorem sourceLocalMellinWeight_norm_integral_ball (n : ℤ) (z : ℂ) (hz : 0 < z.re) :
    (∫ u in sourceLocalMulBall K P n, ‖sourceLocalMellinWeight K P z u‖ ∂μ) =
      sourceLocalMellinShellMass K P * q ^ ((n : ℝ) * z.re) / (1 - q ^ (-z.re)) := by
  have hi := (sourceLocalMellinWeight_integrable_ball K P n z hz).norm
  rw [sourceLocalMulBall_iUnion] at hi ⊢
  rw [integral_iUnion (fun m : ℕ => sourceLocalMulShell_measurable K P (n - (m : ℤ)))
    (sourceLocalMulBall_shells_disjoint K P n) hi]
  simp_rw [sourceLocalMellinWeight_norm_integral_shell]
  have h := sourceLocalMellinRatio_norm_lt_one K P z hz
  rw [tsum_mul_left, (hasSum_geometric_of_lt_one (norm_nonneg _) h).tsum_eq]
  simp only [Complex.norm_cpow_eq_rpow_re_of_pos (sourceLocalNorm_pos K P),
    Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero,
    Complex.neg_re, div_eq_mul_inv]

theorem sourceLocalMellinShellMass_pos : 0 < sourceLocalMellinShellMass K P := by
  apply mul_pos (sourceLocalBall_volume_pos K P 0)
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (sourceLocalMellinQ_gt_one K P))

theorem sourceLocalMellinWeight_norm_integral_ball_le (n : ℤ) (hn : 0 ≤ n)
    (a b : ℝ) (ha : 0 < a) (z : ℂ) (hl : a ≤ z.re) (hh : z.re ≤ b) :
    (∫ u in sourceLocalMulBall K P n, ‖sourceLocalMellinWeight K P z u‖ ∂μ) ≤
      sourceLocalMellinShellMass K P * q ^ ((n : ℝ) * b) / (1 - q ^ (-a)) := by
  have hq := sourceLocalMellinQ_gt_one K P
  rw [sourceLocalMellinWeight_norm_integral_ball K P n z (ha.trans_le hl)]
  apply div_le_div₀ (mul_nonneg (sourceLocalMellinShellMass_pos K P).le (Real.rpow_nonneg
    (sourceLocalNorm_pos K P).le _))
  · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq.le
      (mul_le_mul_of_nonneg_left hh (by exact_mod_cast hn)))
      (sourceLocalMellinShellMass_pos K P).le
  · exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hq (neg_lt_zero.mpr ha))
  · exact sub_le_sub_left (Real.rpow_le_rpow_of_exponent_le hq.le (neg_le_neg hl)) _

end
end ArtinMatthews.SourcePhysical
