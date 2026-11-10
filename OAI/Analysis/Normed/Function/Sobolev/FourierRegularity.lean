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
public import OAI.Analysis.Fourier.BochnerRiesz.MultiplierCompatibility
public import OAI.Analysis.Fourier.Wave.Compatibility


set_option backward.privateInPublic true
@[expose] public section

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

/-- Fourier inversion almost everywhere for L¹ ∩ L² data whose classical
Fourier transform is integrable. No continuity of the input is assumed. -/
theorem ae_fourierInv_fourier {d : ℕ} {f : Space d → ℂ}
    (hf : Integrable f) (hf₂ : MemLp f 2) (hF : Integrable (𝓕 f)) :
    f =ᵐ[volume] 𝓕⁻ (𝓕 f) := by
  let u : OAI.Analysis.Fourier.Wave.WaveL2 d := hf₂.toLp f
  let F : OAI.Analysis.Fourier.Wave.WaveL2 d := (Lp.fourierTransformₗᵢ (Space d) ℂ) u
  have hFAE : (F : Space d → ℂ) =ᵐ[volume] 𝓕 f :=
    OAI.Analysis.Fourier.BochnerRiesz.fourier_toLp_ae hf hf₂
  have hFi : Integrable (F : Space d → ℂ) := hF.congr hFAE.symm
  have hInv := OAI.Analysis.Fourier.Wave.inverseFourierL2_coe F hFi
  have hInv' : (u : Space d → ℂ) =ᵐ[volume] 𝓕⁻ (F : Space d → ℂ) := by
    simpa only [F, LinearIsometryEquiv.symm_apply_apply] using hInv
  exact hf₂.coeFn_toLp.symm.trans (hInv'.trans
    (Eventually.of_forall fun x ↦ Real.fourierInv_congr_ae hFAE x))

/-- Integrable Fourier moments produce an actual smooth representative
of L¹ ∩ L² data, not a regularity assumption on the chosen representative. -/
theorem exists_contDiff_representative_of_fourier_moments {d : ℕ} {N : ℕ∞}
    {f : Space d → ℂ} (hf : Integrable f) (hf₂ : MemLp f 2)
    (hF : ∀ k : ℕ, k ≤ N → Integrable (fun ξ ↦ ‖ξ‖ ^ k * ‖𝓕 f ξ‖)) :
    ∃ g : Space d → ℂ, ContDiff ℝ N g ∧ f =ᵐ[volume] g := by
  refine ⟨𝓕⁻ (𝓕 f), ?_, ?_⟩
  · have hc : ContDiff ℝ N (𝓕 (𝓕 f)) := Real.contDiff_fourier hF
    have heq : 𝓕⁻ (𝓕 f) = fun x ↦ 𝓕 (𝓕 f) (-x) := by
      funext x
      exact Real.fourierInv_eq_fourier_neg _ _
    rw [heq]
    exact hc.comp contDiff_neg
  · have hFi : Integrable (𝓕 f) := by
      apply (integrable_norm_iff (OAI.Analysis.Fourier.BochnerRiesz.continuous_fourier_of_integrable hf).aestronglyMeasurable).mp
      simpa only [pow_zero, one_mul] using hF 0 (by simp)
    exact ae_fourierInv_fourier hf hf₂ hFi

end OAI.Analysis.Normed.Function.Sobolev
