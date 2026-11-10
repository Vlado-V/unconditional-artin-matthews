module

public import ArtinMatthews.SpectralWeylMultipliers
public import ArtinMatthews.SpectralKLAnalysisIntegral
public import ArtinMatthews.SpectralJGaussianProbe
public import ArtinMatthews.SpectralJGaussianTail
public import ArtinMatthews.SpectralBesselKStieltjes
public import ArtinMatthews.SpectralJGaussianProbeTail
public import ArtinMatthews.SpectralJGaussianTailKLBound
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

/-! Exact KL calibration of the Gaussian probe with the actual Weyl multiplier. -/

namespace ArtinMatthews

open MeasureTheory Set OAI.CubicEisenstein

noncomputable section

theorem spectralJGaussianTail_analysisIntegral_eq (F : ℝ → ℂ) (r : ℝ) :
    spectralKLPhysicalAnalysisIntegral (spectralJGaussianTail F) r =
      ∫ y in Ioi (0 : ℝ),
        spectralJGaussianTail F y * schlafliBesselK ((r : ℂ) * Complex.I) y / (y : ℂ) := by
  unfold spectralKLPhysicalAnalysisIntegral
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun y hy => ?_)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    rw [schlafliBesselK_imaginary_eq_realKernel r hy]
    simp only [spectralKLPhysicalCompactDiv, mul_div_assoc]
    ring
  · have h : ¬0 < y := hy
    simp only [spectralKLPhysicalCompactDiv, spectralJGaussianTail, ite_eq_right h, zero_div, mul_zero]

theorem spectralJGaussianProbe_rawKLIntegral_integrable (p r : ℝ) (hp : 0 < p) :
    IntegrableOn (fun y : ℝ =>
      spectralJGaussianTail (spectralJGaussianTransform (spectralJGaussianProbe p)) y *
        schlafliBesselK ((r : ℂ) * Complex.I) y / (y : ℂ)) (Ioi 0) := by
  apply spectralJGaussianTail_KLIntegral_integrable _ _ 4 (by norm_num) _ r
  · exact (spectralJGaussianTransform_continuous _ (spectralJGaussianProbe_continuous p)
      (spectralJGaussianProbe_integrable p hp)).measurable
  · intro w hw
    exact spectralJGaussianProbe_transform_tail_bound p hp w (by linarith)

private theorem probeTail_scale (p : ℝ) (hp : 0 < p) :
    (1 / (2 * p)) * Real.pi / Real.sqrt (1 / (8 * p)) =
      Real.sqrt (8 * Real.pi) * Real.sqrt (Real.pi / p) / 2 := by
  let a : ℝ := 1 / (8 * p)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hsa := (Real.sqrt_pos.mpr ha).ne'
  change (1 / (2 * p)) * Real.pi / Real.sqrt a = _
  have hprod : Real.sqrt (8 * Real.pi) * Real.sqrt (Real.pi / p) * Real.sqrt a = Real.pi / p := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 8 * Real.pi),
      ← Real.sqrt_mul (by positivity : 0 ≤ (8 * Real.pi) * (Real.pi / p))]
    rw [show (8 * Real.pi) * (Real.pi / p) * a = (Real.pi / p) ^ 2 by
      dsimp only [a]
      field_simp [hp.ne']]
    exact Real.sqrt_sq (by positivity)
  apply mul_right_cancel₀ hsa
  rw [div_mul_cancel₀ _ hsa]
  calc
    _ = (Real.pi / p) / 2 := by ring
    _ = (Real.sqrt (8 * Real.pi) * Real.sqrt (Real.pi / p) * Real.sqrt a) / 2 :=
      congrArg (fun z : ℝ => z / 2) hprod.symm
    _ = _ := by ring

theorem spectralJGaussianProbe_rawKLIntegral_closed (p r : ℝ) (hp : 0 < p) :
    (∫ y in Ioi (0 : ℝ),
      spectralJGaussianTail (spectralJGaussianTransform (spectralJGaussianProbe p)) y *
        schlafliBesselK ((r : ℂ) * Complex.I) y / (y : ℂ)) =
      (Real.sqrt (8 * Real.pi) : ℂ) *
        ((Real.sqrt (Real.pi / p) : ℂ) / (2 * (Real.cosh (Real.pi * r) : ℂ)) *
          Complex.exp (-((1 / (8 * p) : ℝ) : ℂ)) *
            schlafliBesselK ((r : ℂ) * Complex.I) (1 / (8 * p))) := by
  let a : ℝ := 1 / (8 * p)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hslice : (∫ y in Ioi (0 : ℝ),
      spectralJGaussianTail (spectralJGaussianTransform (spectralJGaussianProbe p)) y *
        schlafliBesselK ((r : ℂ) * Complex.I) y / (y : ℂ)) =
      (((1 / (2 * p) : ℝ) : ℂ) * Complex.exp (-((2 * a : ℝ) : ℂ))) *
        (∫ y in Ioi (0 : ℝ), Complex.exp (-(y : ℂ)) * schlafliBesselK ((r : ℂ) * Complex.I) y /
          ((Real.sqrt y : ℂ) * ((y + a : ℝ) : ℂ))) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    rw [spectralJGaussianProbe_tail_eq p y hp hy]
    have he : Real.exp (-y - 2 * a) = Real.exp (-(2 * a)) * Real.exp (-y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    change (((Real.sqrt y * (1 / (2 * p)) * Real.exp (-y - 2 * a) / (y + a) : ℝ) : ℂ) *
        schlafliBesselK ((r : ℂ) * Complex.I) y / (y : ℂ)) = _
    rw [he]
    push_cast [Complex.ofReal_exp]
    have hs : (Real.sqrt y : ℂ) ^ 2 = (y : ℂ) := by exact_mod_cast Real.sq_sqrt hy.le
    have hsy : (Real.sqrt y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
    have hdiv : (Real.sqrt y : ℂ) / (y : ℂ) = (Real.sqrt y : ℂ)⁻¹ := by
      rw [← hs, pow_two, div_mul_eq_div_div, div_self hsy, one_div]
    calc
      _ = ((Real.sqrt y : ℂ) / (y : ℂ)) *
          ((((1 / (2 * p) : ℝ) : ℂ) * Complex.exp (-((2 * a : ℝ) : ℂ))) *
            (Complex.exp (-(y : ℂ)) * schlafliBesselK ((r : ℂ) * Complex.I) y /
              ((y : ℂ) + (a : ℂ)))) := by
        push_cast
        ring
      _ = _ := by
        rw [hdiv]
        push_cast
        simp only [div_eq_mul_inv, mul_inv]
        ring
  have hscale : ((1 / (2 * p) : ℝ) : ℂ) * (Real.pi : ℂ) / (Real.sqrt a : ℂ) =
      (Real.sqrt (8 * Real.pi) : ℂ) * (Real.sqrt (Real.pi / p) : ℂ) / 2 := by
    exact_mod_cast probeTail_scale p hp
  have hphase : Complex.exp (-((2 * a : ℝ) : ℂ)) * Complex.exp (a : ℂ) =
      Complex.exp (-(a : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hslice, schlafliBesselK_stieltjes r ha]
  calc
    _ = (((1 / (2 * p) : ℝ) : ℂ) * (Real.pi : ℂ) / (Real.sqrt a : ℂ)) *
        (Complex.exp (-((2 * a : ℝ) : ℂ)) * Complex.exp (a : ℂ)) *
        (schlafliBesselK ((r : ℂ) * Complex.I) a / (Real.cosh (Real.pi * r) : ℂ)) := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ = _ := by
      rw [hscale, hphase]
      change _ = (Real.sqrt (8 * Real.pi) : ℂ) *
        ((Real.sqrt (Real.pi / p) : ℂ) / (2 * (Real.cosh (Real.pi * r) : ℂ)) *
          Complex.exp (-(a : ℂ)) * schlafliBesselK ((r : ℂ) * Complex.I) a)
      simp only [div_eq_mul_inv, mul_inv]
      ring

theorem spectralJGaussianProbe_weylCoefficient_eq (p r : ℝ) (hp : 0 < p) (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), spectralJGaussianProbe p x * spectralWeylJMultiplier r x) /
        (4 * (Real.cosh (Real.pi * r) : ℂ)) =
      (Real.sqrt (Real.pi / p) : ℂ) / (2 * (Real.cosh (Real.pi * r) : ℂ)) *
        Complex.exp (-((1 / (8 * p) : ℝ) : ℂ)) *
          schlafliBesselK ((r : ℂ) * Complex.I) (1 / (8 * p)) := by
  have he : (∫ x in Ioi (0 : ℝ), spectralJGaussianProbe p x * spectralWeylJMultiplier r x) =
      ∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) *
        spectralWeylJMultiplier r x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only [spectralJGaussianProbe]
    rw [Complex.ofReal_exp, show ((-(p * x ^ 2) : ℝ) : ℂ) = -(p : ℂ) * (x : ℂ) ^ 2 by
      push_cast
      ring]
    ring
  rw [he, spectralWeylJMultiplier_gaussian_value hr hp]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem spectralJGaussianProbe_rawKLIntegral_eq (p r : ℝ) (hp : 0 < p) (hr : 0 < r) :
    (∫ y in Ioi (0 : ℝ),
      spectralJGaussianTail (spectralJGaussianTransform (spectralJGaussianProbe p)) y *
        schlafliBesselK ((r : ℂ) * Complex.I) y / (y : ℂ)) =
      (Real.sqrt (8 * Real.pi) : ℂ) *
        ((∫ x in Ioi (0 : ℝ), spectralJGaussianProbe p x * spectralWeylJMultiplier r x) /
          (4 * (Real.cosh (Real.pi * r) : ℂ))) := by
  rw [spectralJGaussianProbe_rawKLIntegral_closed p r hp, spectralJGaussianProbe_weylCoefficient_eq p r hp hr]

theorem spectralJGaussianProbe_KLIntegral_eq_coefficient (p r : ℝ) (hp : 0 < p) (hr : 0 < r) :
    (∫ y in Ioi (0 : ℝ),
      spectralJGaussianTail (spectralJGaussianTransform (spectralJGaussianProbe p)) y *
        schlafliBesselK ((r : ℂ) * Complex.I) y / (y : ℂ)) / (Real.sqrt (8 * Real.pi) : ℂ) =
      (∫ x in Ioi (0 : ℝ), spectralJGaussianProbe p x * spectralWeylJMultiplier r x) /
        (4 * (Real.cosh (Real.pi * r) : ℂ)) := by
  rw [spectralJGaussianProbe_rawKLIntegral_eq p r hp hr]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne')

end
end ArtinMatthews
