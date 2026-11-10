module

public import ArtinMatthews.SpectralKLIntegrableAnalysis
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

/-! Absolute physical/spectral interchange for noncompact inputs with
the actual K0-weighted L1 majorant. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectralKL_majorant_pair_integrable (f g : ℝ → ℂ) (hf : Measurable f)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (hM : Integrable (spectralKLIntegrableMajorant f))
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun p : ℝ × ℝ => (spectralKLRealKernel p.1 p.2 : ℂ)*g p.1*
      spectralKLPhysicalCompactDiv f p.2) (volume.prod volume) := by
  have hb : Integrable (fun p : ℝ × ℝ => ‖g p.1‖*spectralKLIntegrableMajorant f p.2)
      (volume.prod volume) := (hg.integrable_of_hasCompactSupport hgc).norm.mul_prod hM
  have hK : Measurable (fun p : ℝ × ℝ => (spectralKLRealKernel p.1 p.2 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp spectralKLRealKernel_stronglyMeasurable.measurable
  have hD : Measurable (spectralKLPhysicalCompactDiv f) := by
    unfold spectralKLPhysicalCompactDiv
    fun_prop
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (spectralKLRealKernel p.1 p.2 : ℂ)*g p.1*spectralKLPhysicalCompactDiv f p.2)
      (volume.prod volume) := ((hK.mul (hg.measurable.comp measurable_fst)).mul
        (hD.comp measurable_snd)).aestronglyMeasurable
  apply hb.mono' hm
  filter_upwards with p
  calc
    _ = ‖g p.1‖*‖(spectralKLRealKernel p.1 p.2 : ℂ)*spectralKLPhysicalCompactDiv f p.2‖ := by
      rw [norm_mul,norm_mul,norm_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (spectralKLIntegrableMajorant_bound f hfzero p.1 p.2) (norm_nonneg _)

theorem spectralKL_majorant_fubini (f g : ℝ → ℂ) (hf : Measurable f)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) (hM : Integrable (spectralKLIntegrableMajorant f))
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    (∫ x : ℝ, spectralKLSynthesis g x*spectralKLPhysicalCompactDiv f x) =
      ∫ t : ℝ, g t*spectralKLPhysicalAnalysisIntegral f t := by
  have hI := spectralKL_majorant_pair_integrable f g hf hfzero hM hg hgc
  calc
    _ = ∫ x : ℝ, ∫ t : ℝ,
        (spectralKLRealKernel t x : ℂ)*g t*spectralKLPhysicalCompactDiv f x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [integral_mul_const]
      rfl
    _ = ∫ t : ℝ, ∫ x : ℝ,
        (spectralKLRealKernel t x : ℂ)*g t*spectralKLPhysicalCompactDiv f x :=
      (integral_integral_swap hI).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [spectralKLPhysicalAnalysisIntegral,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring

end ArtinMatthews
