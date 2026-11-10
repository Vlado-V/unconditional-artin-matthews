module

public import ArtinMatthews.SpectralKLAnalysisIntegral
public import ArtinMatthews.SpectralKLMacdonaldProfile
public import ArtinMatthews.SpectralKLAnalysisCalibration
public import ArtinMatthews.SpectralKLMacdonaldCompactPairing
public import ArtinMatthews.SpectralKLMacdonaldSpectralFubini
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

/-! The actual two-height Macdonald profile bilinear form is diagonal
under the calibrated KL transform, with compact physical test functions. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralKLPhysicalAnalysisIntegral_measure (f : ℝ → ℂ)
    (hfp : tsupport f ⊆ Ioi (0 : ℝ)) (r : ℝ) :
    (∫ x : ℝ, (spectralKLRealKernel r x : ℂ)*f x ∂spectralKLPhysicalMeasure) =
      spectralKLPhysicalAnalysisIntegral f r := by
  rw [spectralKLPhysicalMeasure,spectralKLPositiveWeightMeasure_complex_integral _ _
    (by fun_prop) (fun x hx => inv_nonneg.mpr hx.le),spectralKLPhysicalAnalysisIntegral_eq f hfp r]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [schlafliBesselK_imaginary_eq_realKernel r hx,Complex.ofReal_inv]
  ring_nf

theorem spectralKLPhysicalAnalysisIntegral_measure_star (g : ℝ → ℂ)
    (hgp : tsupport g ⊆ Ioi (0 : ℝ)) (r : ℝ) :
    (∫ x : ℝ, (spectralKLRealKernel r x : ℂ)*star (g x) ∂spectralKLPhysicalMeasure) =
      star (spectralKLPhysicalAnalysisIntegral g r) := by
  rw [← spectralKLPhysicalAnalysisIntegral_measure g hgp r]
  change _ = (starRingEnd ℂ) (∫ x : ℝ, (spectralKLRealKernel r x : ℂ)*g x ∂spectralKLPhysicalMeasure)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  change _ = star ((spectralKLRealKernel r x : ℂ)*g x)
  rw [star_mul,show star (spectralKLRealKernel r x : ℂ) = (spectralKLRealKernel r x : ℂ) from Complex.conj_ofReal _]
  ring_nf

theorem spectralKLMacdonald_bilinear {y : ℝ} (hy : 0 < y)
    (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    (∫ x : ℝ, (∫ z : ℝ, spectralKLMacdonaldProfile x y z*f z ∂spectralKLPhysicalMeasure)*
      star (g x) ∂spectralKLPhysicalMeasure) =
      ∫ r : ℝ, (2*schlafliBesselK ((r : ℂ)*Complex.I) y)*spectralKLPhysicalAnalysisIntegral f r*
        star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure := by
  let F := spectralKLPhysicalAnalysisIntegral f
  have hFm : Measurable F := (spectralKLPhysicalAnalysisIntegral_continuous f hf hfc hfp).measurable
  have hF : MemLp F 2 spectralKLSpectralMeasure := spectralKLPhysicalAnalysisIntegral_memLp f hf hfc hfp
  calc
    _ = ∫ x : ℝ, (∫ r : ℝ, spectralKLMacdonaldSpectralPair y F g (x,r)
        ∂spectralKLSpectralMeasure) ∂spectralKLPhysicalMeasure := by
      apply integral_congr_ae
      filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
      rw [spectralKLMacdonaldPairing_compact hx hy f hf hfc hfp,← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with r
      rw [spectralKLMacdonaldSpectralPair,schlafliBesselK_imaginary_eq_realKernel r hx,
        schlafliBesselK_imaginary_eq_realKernel r hy]
    _ = ∫ r : ℝ, (∫ x : ℝ, spectralKLMacdonaldSpectralPair y F g (x,r)
        ∂spectralKLPhysicalMeasure) ∂spectralKLSpectralMeasure :=
      spectralKLMacdonaldSpectralPair_swap hy F g hFm hF hg hgc hgp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with r
      calc
        _ = (2*(spectralKLRealKernel r y : ℂ)*F r)*
            (∫ x : ℝ, (spectralKLRealKernel r x : ℂ)*star (g x) ∂spectralKLPhysicalMeasure) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          unfold spectralKLMacdonaldSpectralPair
          ring_nf
        _ = _ := by
          rw [spectralKLPhysicalAnalysisIntegral_measure_star g hgp r,
            schlafliBesselK_imaginary_eq_realKernel r hy]

end ArtinMatthews
