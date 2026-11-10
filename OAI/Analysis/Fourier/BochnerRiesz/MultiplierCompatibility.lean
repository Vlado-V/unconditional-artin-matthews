module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.Fourier.Wave.Multiplier
public import Mathlib.Analysis.CStarAlgebra.Classes
public import OAI.Analysis.Fourier.LocalSmoothing.Definitions
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
public import OAI.Analysis.Fourier.BochnerRiesz.FourierCompatibility
public import OAI.Analysis.Fourier.Wave.AngularTransform
public import OAI.Analysis.Fourier.Wave.Compatibility


set_option backward.privateInPublic true
@[expose] public section

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem continuous_fourier_of_integrable {n : ℕ} {f : Space n → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) := by
  rw [← Real.fourierTransform_toLp (memLp_one_iff_integrable.mpr hf)]
  exact (Real.Lp.fourierTransform _).continuous

theorem fourier_toLp_ae {n : ℕ} {f : Space n → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    (fun ξ ↦ ((Lp.fourierTransformₗᵢ (Space n) ℂ) (hf2.toLp f)) ξ) =ᵐ[volume] 𝓕 f := by
  have hc := hf2.coeFn_toLp
  have hi : Integrable ((hf2.toLp f) : Space n → ℂ) := hf.congr hc.symm
  exact (fourierL2_coe _ hi).trans (Filter.Eventually.of_forall
    (fun ξ ↦ Real.fourier_congr_ae hc ξ))

/-- The natural-domain L² multiplier has its usual inverse-integral
representative for continuous compactly supported symbols and L¹∩L² input. -/
theorem fourierMultiplierL2_coe {n : ℕ} {m f : Space n → ℂ}
    (hm : Continuous m) (hc : HasCompactSupport m) (hf : Integrable f) (hf2 : MemLp f 2)
    (hmf : MemLp (fun ξ ↦ m ξ * ((Lp.fourierTransformₗᵢ (Space n) ℂ) (hf2.toLp f)) ξ) 2) :
    (fun x ↦ ((Lp.fourierTransformₗᵢ (Space n) ℂ).symm (hmf.toLp _)) x) =ᵐ[volume]
      𝓕⁻ (fun ξ ↦ m ξ * (𝓕 f) ξ) := by
  let g : OAI.Analysis.Fourier.Wave.WaveL2 n := hmf.toLp _
  have he : (g : Space n → ℂ) =ᵐ[volume] (fun ξ ↦ m ξ * (𝓕 f) ξ) := by
    filter_upwards [hmf.coeFn_toLp, fourier_toLp_ae hf hf2] with ξ hξ hF
    exact hξ.trans (congrArg (m ξ * ·) hF)
  have hi : Integrable (fun ξ ↦ m ξ * (𝓕 f) ξ) :=
    (hm.mul (continuous_fourier_of_integrable hf)).integrable_of_hasCompactSupport hc.mul_right
  have hg : Integrable (g : Space n → ℂ) := hi.congr he.symm
  exact (OAI.Analysis.Fourier.Wave.inverseFourierL2_coe g hg).trans
    (Filter.Eventually.of_forall (fun x ↦ Real.fourierInv_congr_ae he x))

theorem frequencyHalfWave_zero_eq_fourierInv {n : ℕ} (χ : Space n → ℂ) (h : ℝ)
    (f : Space n → ℂ) :
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ h 0 f =
      𝓕⁻ (fun ξ ↦ χ (h • ((2 * Real.pi) • ξ)) * (𝓕 f) ξ) := by
  funext x
  unfold OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave
  rw [OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
    one_mul, OAI.Analysis.Fourier.Wave.angularFourier_scaled]

theorem fourierMultiplierL2_coe_repr {n : ℕ} {m f : Space n → ℂ} (u : OAI.Analysis.Fourier.Wave.WaveL2 n)
    (hu : (u : Space n → ℂ) =ᵐ[volume] f)
    (hm : Continuous m) (hc : HasCompactSupport m) (hf : Integrable f)
    (hmf : MemLp (fun ξ ↦ m ξ * ((Lp.fourierTransformₗᵢ (Space n) ℂ) u) ξ) 2) :
    (fun x ↦ (OAI.Analysis.Fourier.Wave.fourierMultiplierL2 m u hmf) x) =ᵐ[volume]
      𝓕⁻ (fun ξ ↦ m ξ * (𝓕 f) ξ) := by
  have hF := (fourierL2_coe u (hf.congr hu.symm)).trans
    (Filter.Eventually.of_forall (fun ξ ↦ Real.fourier_congr_ae hu ξ))
  let g : OAI.Analysis.Fourier.Wave.WaveL2 n := hmf.toLp _
  have he : (g : Space n → ℂ) =ᵐ[volume] (fun ξ ↦ m ξ * (𝓕 f) ξ) := by
    filter_upwards [hmf.coeFn_toLp, hF] with ξ hξ hFξ
    exact hξ.trans (congrArg (m ξ * ·) hFξ)
  have hi : Integrable (fun ξ ↦ m ξ * (𝓕 f) ξ) :=
    (hm.mul (continuous_fourier_of_integrable hf)).integrable_of_hasCompactSupport hc.mul_right
  have hg : Integrable (g : Space n → ℂ) := hi.congr he.symm
  exact (OAI.Analysis.Fourier.Wave.inverseFourierL2_coe g hg).trans
    (Filter.Eventually.of_forall (fun x ↦ Real.fourierInv_congr_ae he x))

end OAI.Analysis.Fourier.BochnerRiesz
