module

public import ArtinMatthews.SpectralHyperbolicComplexGreen
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Order.CompletePartialOrder
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

/-! Genuine compact-test Green transfer for C² plane functions. Smoothness
beyond two derivatives is not assumed for the source. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace ArtinMatthews

local instance : (volume : Measure (ℝ×ℝ)).IsAddHaarMeasure := by
  change (volume.prod volume : Measure (ℝ×ℝ)).IsAddHaarMeasure
  infer_instance

theorem spectral_plane_weak_pairing_C1 (F φ : ℝ×ℝ → ℂ)
    (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) (v : ℝ×ℝ) :
    (∫ p, F p*fderiv ℝ φ p v) = -∫ p, fderiv ℝ F p v*φ p := by
  have hDF := (hF.continuous_fderiv (by norm_num)).clm_apply (continuous_const : Continuous (fun _ : ℝ×ℝ => v))
  have hDφ := (hφ.continuous_fderiv (by norm_num)).clm_apply (continuous_const : Continuous (fun _ : ℝ×ℝ => v))
  have hsD := hs.fderiv_apply ℝ v
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hDF.mul hφ.continuous).integrable_of_hasCompactSupport hs.mul_left)
    ((hF.continuous.mul hDφ).integrable_of_hasCompactSupport hsD.mul_left)
    ((hF.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hs.mul_left)
    (fun p _ => hF.differentiable (by norm_num) p)
    (fun p _ => hφ.differentiable (by norm_num) p)

theorem spectralPlaneSecond_transfer_C2 (φ F : ℝ×ℝ → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hF : ContDiff ℝ 2 F) (hs : HasCompactSupport φ)
    (i : Fin 2) :
    (∫ p, inner ℂ (spectralPlaneSecond φ i p) (F p))=
      ∫ p, inner ℂ (φ p) (spectralPlaneSecond F i p) := by
  let v := spectralPlaneDirection i
  have hDφ : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDF : ContDiff ℝ 1 (fun p => fderiv ℝ F p v) :=
    (hF.fderiv_right (by norm_num : (1:ℕ∞ω)+1≤2)).clm_apply contDiff_const
  have hsφ : ContDiff ℝ ∞ (fun p => star (φ p)) := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hφ
  have hsDφ : ContDiff ℝ ∞ (fun p => star (fderiv ℝ φ p v)) :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hDφ
  have h1 := spectral_plane_weak_pairing_C1 F (fun p => star (fderiv ℝ φ p v))
    (hF.of_le (by norm_num)) (hsDφ.of_le (by simp))
    ((hs.fderiv_apply ℝ v).comp_left (by simp)) v
  have h2 := spectral_plane_weak_pairing_C1 (fun p => fderiv ℝ F p v) (fun p => star (φ p))
    hDF (hsφ.of_le (by simp)) (hs.comp_left (by simp)) v
  have hstar1 (p : ℝ×ℝ) : fderiv ℝ (fun q => star (φ q)) p v=star (fderiv ℝ φ p v) := by
    rw [fderiv_star,ContinuousLinearMap.comp_apply]
    rfl
  have hstar2 (p : ℝ×ℝ) : fderiv ℝ (fun q => star (fderiv ℝ φ q v)) p v=
      star (fderiv ℝ (fun q => fderiv ℝ φ q v) p v) := by
    rw [fderiv_star,ContinuousLinearMap.comp_apply]
    rfl
  simp_rw [hstar2] at h1
  simp_rw [hstar1] at h2
  rw [h2,neg_neg] at h1
  simpa only [spectralPlaneSecond,RCLike.inner_apply,starRingEnd_apply,mul_comm,v] using h1

end ArtinMatthews
