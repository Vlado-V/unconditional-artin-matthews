module

public import ArtinMatthews.SpectralKLWeightedMeasures
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

def spectralJGaussianTail (F : ℝ → ℂ) (Y : ℝ) : ℂ :=
  if 0 < Y then
    ((Real.sqrt Y * Real.exp Y : ℝ) : ℂ) *
      ∫ w in Ioi (2 : ℝ), (Real.exp (-(Y * w)) : ℂ) * F w
  else 0

theorem spectralJGaussianTail_measurable (F : ℝ → ℂ) (hF : Measurable F) :
    Measurable (spectralJGaussianTail F) := by
  have hm : StronglyMeasurable (fun p : ℝ × ℝ =>
      (Real.exp (-(p.1 * p.2)) : ℂ) * F p.2) := by
    apply Measurable.stronglyMeasurable
    have he : Measurable (fun p : ℝ × ℝ => (Real.exp (-(p.1 * p.2)) : ℂ)) := by
      fun_prop
    exact he.mul (hF.comp measurable_snd)
  have hi : Measurable (fun Y : ℝ =>
      ∫ w in Ioi (2 : ℝ), (Real.exp (-(Y * w)) : ℂ) * F w) :=
    hm.integral_prod_right'.measurable
  unfold spectralJGaussianTail
  have hp : Measurable (fun Y : ℝ => ((Real.sqrt Y * Real.exp Y : ℝ) : ℂ)) := by
    fun_prop
  exact Measurable.ite measurableSet_Ioi (hp.mul hi) measurable_const

theorem spectralJGaussianTail_bound (F : ℝ → ℂ)
    (hF : IntegrableOn F (Ioi (2 : ℝ))) (Y : ℝ) (hY : 0 < Y) :
    ‖spectralJGaussianTail F Y‖ ≤
      Real.sqrt Y * Real.exp (-Y) * (∫ w in Ioi (2 : ℝ), ‖F w‖) := by
  have hi : ‖∫ w in Ioi (2 : ℝ), (Real.exp (-(Y * w)) : ℂ) * F w‖ ≤
      Real.exp (-(2 * Y)) * (∫ w in Ioi (2 : ℝ), ‖F w‖) := by
    calc
      _ ≤ ∫ w in Ioi (2 : ℝ), Real.exp (-(2 * Y)) * ‖F w‖ := by
        apply norm_integral_le_of_norm_le (hF.norm.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
        change 2 < w at hw
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := integral_const_mul _ _
  rw [spectralJGaussianTail, if_pos hY, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ Real.sqrt Y * Real.exp Y)]
  calc
    _ ≤ (Real.sqrt Y * Real.exp Y) *
        (Real.exp (-(2 * Y)) * (∫ w in Ioi (2 : ℝ), ‖F w‖)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = Real.sqrt Y * (Real.exp Y * Real.exp (-(2 * Y))) *
        (∫ w in Ioi (2 : ℝ), ‖F w‖) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      have he : Y + -(2 * Y) = -Y := by ring
      rw [he]

theorem spectralJGaussianTail_memLp (F : ℝ → ℂ) (hFm : Measurable F)
    (hF : IntegrableOn F (Ioi (2 : ℝ))) :
    MemLp (spectralJGaussianTail F) 2 spectralKLPhysicalMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (spectralJGaussianTail_measurable F hFm).aestronglyMeasurable).mpr
  rw [spectralKLPhysicalMeasure, spectralKLPositiveWeightMeasure_integrable_iff _ _
    (by fun_prop) (fun Y hY => inv_nonneg.mpr hY.le)]
  let D : ℝ := ∫ w in Ioi (2 : ℝ), ‖F w‖
  have hD : 0 ≤ D := integral_nonneg fun _ => norm_nonneg _
  have hi : IntegrableOn (fun Y : ℝ => D ^ 2 * Real.exp (-(2 * Y)))
      (Ioi (0 : ℝ)) := by
    have he : IntegrableOn (fun Y : ℝ => Real.exp (-(2 * Y))) (Ioi (0 : ℝ)) := by
      simpa only [neg_mul] using
        (integrableOn_exp_mul_Ioi (a := -(2 : ℝ)) (by norm_num) 0)
    exact he.const_mul (D ^ 2)
  apply hi.mono'
    (((by fun_prop : Measurable (fun Y : ℝ => Y⁻¹)).mul
      ((spectralJGaussianTail_measurable F hFm).norm.pow_const 2)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
  change 0 < Y at hY
  change ‖Y⁻¹ * ‖spectralJGaussianTail F Y‖ ^ 2‖ ≤ D ^ 2 * Real.exp (-(2 * Y))
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ Y⁻¹ * ‖spectralJGaussianTail F Y‖ ^ 2)]
  have hb := spectralJGaussianTail_bound F hF Y hY
  have hs : ‖spectralJGaussianTail F Y‖ ^ 2 ≤
      (Real.sqrt Y * Real.exp (-Y) * D) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  calc
    _ ≤ Y⁻¹ * (Real.sqrt Y * Real.exp (-Y) * D) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hY.le)
    _ = D ^ 2 * Real.exp (-(2 * Y)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hY.le, pow_two (Real.exp (-Y)), ← Real.exp_add]
      have he : -Y + -Y = -(2 * Y) := by ring
      rw [he]
      field_simp

end
end ArtinMatthews
