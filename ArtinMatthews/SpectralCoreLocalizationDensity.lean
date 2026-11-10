module

public import ArtinMatthews.SpectralCoreLocalizationCoordinates
public import ArtinMatthews.SpectralCoreLocalizationBounds
public import ArtinMatthews.SpectralCoreLocalizationDerivatives
public import ArtinMatthews.SpectralRellichGreenEnergy
public import ArtinMatthews.SpectralRellichHyperbolic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual localization density is dominated by hyperbolic chart
mass and Dirichlet energy with a constant depending only on the cutoff. -/

namespace ArtinMatthews
noncomputable section

open MeasureTheory Set
open scoped ContDiff SchwartzMap LineDeriv

theorem spectralCoreLocalizationFun_chart_bound
    (φ : SchwartzMap (ℝ × ℝ) ℂ) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) {M b : ℝ} (hM : 0 ≤ M)
    (hφ : ∀ p, ‖φ p‖ ≤ M ∧ ‖spectralPlanePartialX φ p‖ ≤ M ∧
      ‖spectralPlanePartialY φ p‖ ≤ M) {p : ℝ × ℝ} (hp : 0 < p.2) (hpb : p.2 ≤ b) :
    ‖spectralCoreLocalizationFun φ F p‖^2+
      (‖spectralPlanePartialX (spectralCoreLocalizationFun φ F) p‖^2+
        ‖spectralPlanePartialY (spectralCoreLocalizationFun φ F) p‖^2) ≤
      (5*M^2*(b^2+1))*(spectralCoreChartEnergy F p/p.2^2) := by
  let U : ℝ := ‖spectralSectionPlane F p‖^2
  let E : ℝ := ‖spectralPlanePartialX (spectralSectionPlane F) p‖^2+
    ‖spectralPlanePartialY (spectralSectionPlane F) p‖^2
  have hU : 0 ≤ U := sq_nonneg _
  have hE : 0 ≤ E := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hy2 : 0 < p.2^2 := sq_pos_of_pos hp
  have hband : p.2^2 ≤ b^2 := pow_le_pow_left₀ hp.le hpb 2
  have hmass : U ≤ b^2*(U/p.2^2) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hy2).mpr
    nlinarith [mul_le_mul_of_nonneg_left hband hU]
  have hweight : 0 ≤ U/p.2^2 := div_nonneg hU hy2.le
  have hc0 : 5*M^2*b^2 ≤ 5*M^2*(b^2+1) := by nlinarith [sq_nonneg M]
  have hc1 : 2*M^2 ≤ 5*M^2*(b^2+1) := by
    nlinarith [sq_nonneg M, mul_nonneg (sq_nonneg M) (sq_nonneg b)]
  have henergy : spectralCoreChartEnergy F p = U+p.2^2*E := by
    rw [spectralCoreChartEnergy, spectralSectionPlane_energy F hF hp]
  have he : (U+p.2^2*E)/p.2^2 = U/p.2^2+E := by field_simp
  calc
    _ ≤ 5*M^2*U+2*M^2*E := spectralCoreLocalizationFun_pointwise_energy φ F hF hM hφ hp
    _ ≤ 5*M^2*(b^2*(U/p.2^2))+2*M^2*E :=
      add_le_add (mul_le_mul_of_nonneg_left hmass (by positivity)) le_rfl
    _ = (5*M^2*b^2)*(U/p.2^2)+(2*M^2)*E := by ring
    _ ≤ (5*M^2*(b^2+1))*(U/p.2^2)+(5*M^2*(b^2+1))*E :=
      add_le_add (mul_le_mul_of_nonneg_right hc0 hweight) (mul_le_mul_of_nonneg_right hc1 hE)
    _ = _ := by rw [henergy, he]; ring

def spectralPlaneH1Density (G : SchwartzMap (ℝ × ℝ) ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖G p‖^2+(‖spectralPlanePartialX G p‖^2+‖spectralPlanePartialY G p‖^2)

theorem spectralPlaneH1Density_integrable (G : SchwartzMap (ℝ × ℝ) ℂ)
    (hc : HasCompactSupport (G : ℝ × ℝ → ℂ)) : Integrable (spectralPlaneH1Density G) := by
  have hx : HasCompactSupport (fun p => fderiv ℝ (G : ℝ × ℝ → ℂ) p ((1,0) : ℝ × ℝ)) :=
    hc.fderiv_apply ℝ _
  have hy : HasCompactSupport (fun p => fderiv ℝ (G : ℝ × ℝ → ℂ) p ((0,1) : ℝ × ℝ)) :=
    hc.fderiv_apply ℝ _
  have hdx : HasCompactSupport (fun p => (∂_{((1,0) : ℝ × ℝ)} G) p) := by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using hx
  have hdy : HasCompactSupport (fun p => (∂_{((0,1) : ℝ × ℝ)} G) p) := by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using hy
  have hm := spectral_plane_normsq_integrable G.continuous hc
  have hmx := spectral_plane_normsq_integrable (∂_{((1,0) : ℝ × ℝ)} G).continuous hdx
  have hmy := spectral_plane_normsq_integrable (∂_{((0,1) : ℝ × ℝ)} G).continuous hdy
  convert hm.add (hmx.add hmy) using 1
  funext p
  simp only [spectralPlaneH1Density, spectralPlanePartialX_schwartz,
    spectralPlanePartialY_schwartz, Pi.add_apply]

theorem spectralPlaneH1Density_eq_zero {G : SchwartzMap (ℝ × ℝ) ℂ}
    {S : Set (ℝ × ℝ)} (hG : tsupport G ⊆ S) {p : ℝ × ℝ} (hp : p ∉ S) :
    spectralPlaneH1Density G p = 0 := by
  have hnot : p ∉ tsupport G := fun hh => hp (hG hh)
  have hz : G p = 0 := by
    by_contra hh
    exact hnot (subset_tsupport _ hh)
  have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot
  rw [spectralPlaneH1Density, hz, spectralPlanePartialX_eq_fderiv G.differentiableAt,
    spectralPlanePartialY_eq_fderiv G.differentiableAt, hd]
  simp

end
end ArtinMatthews
