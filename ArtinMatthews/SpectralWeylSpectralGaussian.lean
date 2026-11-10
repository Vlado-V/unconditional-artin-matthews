module

public import ArtinMatthews.SpectralWeylSpectralGaussianIntegrable
public import ArtinMatthews.SpectralKLAnalysisIntegral
public import ArtinMatthews.SpectralKLAnalysisCalibration
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

/-! Evaluated Gaussian actions of the actual compact-test J/K spectral
bilinear forms.  The swap uses proved absolute integrability. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralWeyl_gaussian_spectral_swap (M : ℝ → ℝ → ℂ) (p : ℝ) (F G : ℝ → ℂ)
    (hi : Integrable (spectralWeylGaussianSpectralIntegrand M p F G)
      ((volume.restrict (Ioi (0 : ℝ))).prod spectralKLSpectralMeasure)) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (∫ r : ℝ, M r X*F r*star (G r) ∂spectralKLSpectralMeasure)) =
      ∫ r : ℝ, (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*M r X)*
        F r*star (G r) ∂spectralKLSpectralMeasure := by
  calc
    _ = ∫ X in Ioi (0 : ℝ), ∫ r : ℝ,
        spectralWeylGaussianSpectralIntegrand M p F G (X,r) ∂spectralKLSpectralMeasure := by
      apply integral_congr_ae
      filter_upwards with X
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with r
      unfold spectralWeylGaussianSpectralIntegrand
      ring_nf
    _ = ∫ r : ℝ, (∫ X in Ioi (0 : ℝ),
        spectralWeylGaussianSpectralIntegrand M p F G (X,r)) ∂spectralKLSpectralMeasure :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with r
      rw [← integral_mul_const,← integral_mul_const]
      rfl

theorem spectralWeylJ_gaussian_spectral {p : ℝ} (hp : 1/4 < p)
    (F G : ℝ → ℂ) (hcF : Continuous F) (hcG : Continuous G)
    (hF : MemLp F 2 spectralKLSpectralMeasure) (hG : MemLp G 2 spectralKLSpectralMeasure) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (∫ r : ℝ, spectralWeylJMultiplier r X*F r*star (G r) ∂spectralKLSpectralMeasure)) =
      ∫ r : ℝ, (2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp (-((1/(8*p) : ℝ) : ℂ))*
        schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)))*F r*star (G r)
          ∂spectralKLSpectralMeasure := by
  rw [spectralWeyl_gaussian_spectral_swap _ p F G
    (spectralWeylJGaussianSpectralIntegrand_integrable hp F G hcF hcG hF hG)]
  apply integral_congr_ae
  filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with r hr
  rw [spectralWeylJMultiplier_gaussian_value hr (by linarith : 0 < p)]

theorem spectralWeylK_gaussian_spectral {p : ℝ} (hp : 1/4 < p)
    (F G : ℝ → ℂ) (hcF : Continuous F) (hcG : Continuous G)
    (hF : MemLp F 2 spectralKLSpectralMeasure) (hG : MemLp G 2 spectralKLSpectralMeasure) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (∫ r : ℝ, spectralWeylKMultiplier r X*F r*star (G r) ∂spectralKLSpectralMeasure)) =
      ∫ r : ℝ, (2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp ((1/(8*p) : ℝ) : ℂ)*
        schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)))*F r*star (G r)
          ∂spectralKLSpectralMeasure := by
  rw [spectralWeyl_gaussian_spectral_swap _ p F G
    (spectralWeylKGaussianSpectralIntegrand_integrable hp F G hcF hcG hF hG)]
  apply integral_congr_ae
  filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with r hr
  rw [spectralWeylKMultiplier_gaussian_value hr (by linarith : 0 < p)]

theorem spectralWeylJ_gaussian_compact_analysis {p : ℝ} (hp : 1/4 < p)
    (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (∫ r : ℝ, spectralWeylJMultiplier r X*spectralKLPhysicalAnalysisIntegral f r*
        star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure)) =
      ∫ r : ℝ, (2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp (-((1/(8*p) : ℝ) : ℂ))*
        schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)))*spectralKLPhysicalAnalysisIntegral f r*
          star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure :=
  spectralWeylJ_gaussian_spectral hp _ _
    (spectralKLPhysicalAnalysisIntegral_continuous f hf hfc hfp)
    (spectralKLPhysicalAnalysisIntegral_continuous g hg hgc hgp)
    (spectralKLPhysicalAnalysisIntegral_memLp f hf hfc hfp)
    (spectralKLPhysicalAnalysisIntegral_memLp g hg hgc hgp)

theorem spectralWeylK_gaussian_compact_analysis {p : ℝ} (hp : 1/4 < p)
    (f g : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (∫ r : ℝ, spectralWeylKMultiplier r X*spectralKLPhysicalAnalysisIntegral f r*
        star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure)) =
      ∫ r : ℝ, (2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp ((1/(8*p) : ℝ) : ℂ)*
        schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)))*spectralKLPhysicalAnalysisIntegral f r*
          star (spectralKLPhysicalAnalysisIntegral g r) ∂spectralKLSpectralMeasure :=
  spectralWeylK_gaussian_spectral hp _ _
    (spectralKLPhysicalAnalysisIntegral_continuous f hf hfc hfp)
    (spectralKLPhysicalAnalysisIntegral_continuous g hg hgc hgp)
    (spectralKLPhysicalAnalysisIntegral_memLp f hf hfc hfp)
    (spectralKLPhysicalAnalysisIntegral_memLp g hg hgc hgp)

end ArtinMatthews
