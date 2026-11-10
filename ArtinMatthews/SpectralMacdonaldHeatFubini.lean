module

public import ArtinMatthews.SpectralMacdonaldHeatKernel
public import ArtinMatthews.SpectralMacdonaldCoordinates
public import ArtinMatthews.SpectralMacdonaldConvolution
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute heat/Fourier Fubini for the genuine Macdonald kernel. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology

namespace ArtinMatthews

def spectralMacdonaldHeatFourier (x y t : ℝ) (p : ℝ × ℝ) : ℂ :=
  spectralMacdonaldHeatKernel (spectralMacdonaldRadius x y p.1) p.2*
    Complex.exp (((t*p.1 : ℝ) : ℂ)*Complex.I)

theorem spectralMacdonaldHeatFourier_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    Integrable (spectralMacdonaldHeatFourier x y t) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : AEStronglyMeasurable (spectralMacdonaldHeatFourier x y t)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    unfold spectralMacdonaldHeatFourier spectralMacdonaldHeatKernel spectralMacdonaldRadius
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards with w
    change Integrable (fun r : ℝ => spectralMacdonaldHeatKernel (spectralMacdonaldRadius x y w) r*
      Complex.exp (((t*w : ℝ) : ℂ)*Complex.I)) (volume.restrict (Ioi (0 : ℝ)))
    exact (spectralMacdonaldHeatKernel_integrable (spectralMacdonaldRadius_pos hx hy w)).mul_const _
  · have hnorm (w : ℝ) :
        (∫ r in Ioi (0 : ℝ), ‖spectralMacdonaldHeatFourier x y t (w,r)‖) =
          (2*schlafliBesselK 0 (spectralMacdonaldRadius x y w)).re := by
      calc
        _ = ∫ r in Ioi (0 : ℝ), (spectralMacdonaldHeatKernel (spectralMacdonaldRadius x y w) r).re := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
          unfold spectralMacdonaldHeatFourier
          rw [norm_mul,Complex.norm_exp]
          simp only [Complex.mul_re,Complex.ofReal_re,Complex.I_re,Complex.ofReal_im,
            Complex.I_im,mul_zero,sub_zero,Real.exp_zero,mul_one]
          exact (spectralMacdonaldHeatKernel_re_eq_norm _ hr).symm
        _ = (∫ r in Ioi (0 : ℝ), spectralMacdonaldHeatKernel (spectralMacdonaldRadius x y w) r).re := by
          exact integral_re (spectralMacdonaldHeatKernel_integrable (spectralMacdonaldRadius_pos hx hy w))
        _ = _ := by rw [spectralMacdonaldHeatKernel_integral (spectralMacdonaldRadius_pos hx hy w)]
    have hi := (spectralMacdonald_radius_kernel_integrable hx hy).re.const_mul 2
    apply hi.congr
    filter_upwards with w
    rw [hnorm]
    change 2*(schlafliBesselK 0 (spectralMacdonaldRadius x y w)).re =
      (2*schlafliBesselK 0 (spectralMacdonaldRadius x y w)).re
    norm_num [Complex.mul_re]

theorem spectralMacdonaldHeatFourier_integral_r {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t w : ℝ) :
    (∫ r in Ioi (0 : ℝ), spectralMacdonaldHeatFourier x y t (w,r)) =
      2*schlafliBesselK 0 (spectralMacdonaldRadius x y w)*Complex.exp (((t*w : ℝ) : ℂ)*Complex.I) := by
  unfold spectralMacdonaldHeatFourier
  dsimp only
  rw [integral_mul_const,spectralMacdonaldHeatKernel_integral (spectralMacdonaldRadius_pos hx hy w)]

end ArtinMatthews
