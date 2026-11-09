module

public import ArtinMatthews.SpectralJRegularizer
public import Mathlib.Analysis.SpecialFunctions.Exp


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Filter Set
open scoped Topology
noncomputable section

def spectralJRegularizationMultiplier (L l : ℝ) : ℝ :=
  1 - Real.exp (-(L * l))

theorem spectralJRegularizationMultiplier_bounds {L l : ℝ} (hL : 0 ≤ L) (hl : 0 ≤ l) :
    0 ≤ spectralJRegularizationMultiplier L l ∧ spectralJRegularizationMultiplier L l ≤ 1 := by
  have hE : Real.exp (-(L * l)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hL hl))
  unfold spectralJRegularizationMultiplier
  constructor <;> linarith [Real.exp_pos (-(L * l))]

theorem spectralJRegularizationMultiplier_tendsto {l : ℝ} (hl : 0 < l) :
    Tendsto (fun L : ℝ => spectralJRegularizationMultiplier L l) atTop (𝓝 1) := by
  have hE : Tendsto (fun L : ℝ => Real.exp (-(L * l))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hl)
  simpa only [spectralJRegularizationMultiplier, sub_zero] using tendsto_const_nhds.sub hE

theorem spectralJRegularizer_exp_tendsto {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun L : ℝ => Complex.exp (-(L : ℂ) * w)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hE : Tendsto (fun L : ℝ => Real.exp (-(L * w.re))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hw)
  convert hE using 1
  funext L
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  ring

theorem spectralJRegularizerPrimitive_tendsto {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun L : ℝ => spectralJRegularizerPrimitive L w) atTop (𝓝 w⁻¹) := by
  have hw0 : w ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hw; linarith
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℂ)) atTop (𝓝 1)).sub
    (spectralJRegularizer_exp_tendsto hw)).div_const w
  simpa only [spectralJRegularizerPrimitive_of_ne_zero _ hw0, sub_zero, one_div] using h

end
end ArtinMatthews
