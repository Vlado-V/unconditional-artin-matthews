module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.CStarAlgebra.Classes
public import OAI.Analysis.Fourier.Wave.Basic
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

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem fourier_integral_pairing {n : ℕ} (g : Space n → ℂ)
    (hg : Integrable g) (φ : SchwartzMap (Space n) ℂ) :
    (∫ ξ, (𝓕 φ) ξ * g ξ) = ∫ x, φ x * (𝓕 g) x := by
  have hL : (innerₗ (Space n)).flip = innerₗ (Space n) := by
    ext x y
    simp []
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := innerₗ (Space n))
    (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner φ.integrable hg
  rw [hL] at h
  have hφ (ξ : Space n) : (𝓕 φ) ξ = (𝓕 (φ : Space n → ℂ)) ξ :=
    congrFun (SchwartzMap.fourier_coe φ) ξ
  simp_rw [hφ]
  change (∫ ξ, VectorFourier.fourierIntegral Real.fourierChar volume
    (innerₗ (Space n)) φ ξ * g ξ) =
    ∫ x, φ x * VectorFourier.fourierIntegral Real.fourierChar volume
      (innerₗ (Space n)) g x
  simpa only [smul_eq_mul] using h

theorem fourierL2_integral_pairing {n : ℕ} (g : OAI.Analysis.Fourier.Wave.WaveL2 n)
    (φ : SchwartzMap (Space n) ℂ) :
    (∫ x, φ x * ((Lp.fourierTransformₗᵢ (Space n) ℂ) g) x) =
      ∫ ξ, (𝓕 φ) ξ * g ξ := by
  have h := congrArg (fun T : TemperedDistribution (Space n) ℂ ↦ T φ)
    (Lp.fourier_toTemperedDistribution_eq g)
  simp only [TemperedDistribution.fourier_apply,
    Lp.toTemperedDistribution_apply, smul_eq_mul] at h
  exact h.symm

/-- The ordinary Fourier integral and the unitary L² Fourier transform agree
for every L¹ ∩ L² function, without a smoothness assumption. -/
theorem fourierL2_coe {n : ℕ} (g : OAI.Analysis.Fourier.Wave.WaveL2 n)
    (hg : Integrable (g : Space n → ℂ)) :
    (fun x ↦ ((Lp.fourierTransformₗᵢ (Space n) ℂ) g) x) =ᵐ[volume]
      𝓕 (g : Space n → ℂ) := by
  have hc : Continuous (𝓕 (g : Space n → ℂ)) := by
    rw [← Real.fourierTransform_toLp (memLp_one_iff_integrable.mpr hg)]
    exact (Real.Lp.fourierTransform _).continuous
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp ((Lp.fourierTransformₗᵢ (Space n) ℂ) g)).locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro ψ hψ hsψ
  have hsc : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hsψ.comp_left rfl
  have hdiff : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ) := by fun_prop
  let φ := hsc.toSchwartzMap hdiff
  have h := (fourierL2_integral_pairing g φ).trans
    (fourier_integral_pairing (g : Space n → ℂ) hg φ)
  simpa [φ, Complex.real_smul] using h

end OAI.Analysis.Fourier.BochnerRiesz
