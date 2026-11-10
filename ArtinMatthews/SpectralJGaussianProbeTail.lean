module

public import ArtinMatthews.SpectralJGaussianProbe
public import ArtinMatthews.SpectralJGaussianTail
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

/-! Exact positive Gaussian probe on the raw forward-J tail. -/

namespace ArtinMatthews

open MeasureTheory Set

noncomputable section

theorem spectralJGaussianProbe_transform_integrableOn_tail (p : ℝ) (hp : 0 < p) :
    IntegrableOn (spectralJGaussianTransform (spectralJGaussianProbe p)) (Ioi (2 : ℝ)) := by
  have hi := integrableOn_exp_mul_Ioi (a := -(1 / (8 * p)))
    (neg_neg_of_pos (by positivity)) 2
  apply (hi.ofReal.const_mul ((1 / (2 * p) : ℝ) : ℂ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw.le
  change ((1 / (2 * p) : ℝ) : ℂ) * (Real.exp (-(1 / (8 * p)) * w) : ℂ) =
    spectralJGaussianTransform (spectralJGaussianProbe p) w
  rw [spectralJGaussianProbe_transform p w hp hw0, Complex.ofReal_mul,
    show -(1 / (8 * p)) * w = -w / (8 * p) by ring]

theorem spectralJGaussianProbe_transform_tail_bound (p : ℝ) (hp : 0 < p)
    (w : ℝ) (hw : 0 < w) :
    ‖spectralJGaussianTransform (spectralJGaussianProbe p) w‖ ≤ 4 / w := by
  let u : ℝ := w / (8 * p)
  have he : u * Real.exp (-u) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_one (Real.exp_pos _)).mpr (by linarith [Real.add_one_le_exp u])
  rw [spectralJGaussianProbe_transform p w hp hw.le, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (2 * p) * Real.exp (-w / (8 * p)))]
  apply (le_div_iff₀ hw).mpr
  rw [show -w / (8 * p) = -u by simp only [u, neg_div]]
  calc
    _ = 4 * (u * Real.exp (-u)) := by dsimp only [u]; ring
    _ ≤ _ := by linarith

/-- The literal tail has no factor of `1 / √(8π)`. -/
theorem spectralJGaussianProbe_tail_eq (p y : ℝ) (hp : 0 < p) (hy : 0 < y) :
    spectralJGaussianTail (spectralJGaussianTransform (spectralJGaussianProbe p)) y =
      ((Real.sqrt y * (1 / (2 * p)) * Real.exp (-y - 2 * (1 / (8 * p))) /
        (y + 1 / (8 * p)) : ℝ) : ℂ) := by
  let a : ℝ := 1 / (8 * p)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hslice : (∫ w in Ioi (2 : ℝ), (Real.exp (-(y * w)) : ℂ) *
      spectralJGaussianTransform (spectralJGaussianProbe p) w) =
      ((1 / (2 * p) : ℝ) : ℂ) * (∫ w in Ioi (2 : ℝ), (Real.exp (-(y + a) * w) : ℂ)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro w hw
    have hw0 : 0 ≤ w := le_trans (by norm_num) hw.le
    dsimp only
    rw [spectralJGaussianProbe_transform p w hp hw0]
    simp only [← Complex.ofReal_mul, Complex.ofReal_inj]
    have he : Real.exp (-(y * w)) * Real.exp (-w / (8 * p)) =
        Real.exp (-(y + a) * w) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [a]
      ring
    rw [← he]
    ring
  have hmass : (∫ w in Ioi (2 : ℝ), (Real.exp (-(y + a) * w) : ℂ)) =
      ((Real.exp (-(y + a) * 2) / (y + a) : ℝ) : ℂ) := by
    rw [integral_complex_ofReal,
      integral_exp_mul_Ioi (a := -(y + a)) (neg_neg_of_pos (add_pos hy ha))]
    simp only [div_neg, neg_div, neg_neg]
  rw [spectralJGaussianTail, ite_eq_left hy, hslice, hmass]
  simp only [← Complex.ofReal_mul, Complex.ofReal_inj]
  have he : Real.exp y * Real.exp (-(y + a) * 2) = Real.exp (-y - 2 * a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.sqrt y * (1 / (2 * p)) * (Real.exp y * Real.exp (-(y + a) * 2)) / (y + a) := by
      ring
    _ = _ := by rw [he]

end
end ArtinMatthews
