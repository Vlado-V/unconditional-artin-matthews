module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Filter Complex
open scoped Topology
noncomputable section

theorem spectral_half_strip_identity (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, |z.re| ≤ 1 / 2 → DifferentiableAt ℂ F z)
    (hG : ∀ z : ℂ, |z.re| ≤ 1 / 2 → DifferentiableAt ℂ G z)
    (haxis : ∀ t : ℝ, F ((t : ℂ) * I) = G ((t : ℂ) * I)) :
    ∀ z : ℂ, |z.re| ≤ 1 / 2 → F z = G z := by
  let S : Set ℂ := {z | |z.re| < 1 / 2}
  let T : Set ℂ := {z | |z.re| ≤ 1 / 2}
  have hSo : IsOpen S := isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hSconvex : Convex ℝ S := by
    have heq : S = Complex.reCLM ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      ext z
      simp only [S, mem_preimage, mem_Ioo, mem_ofPred_eq, Complex.reCLM_apply, abs_lt]
    rw [heq]
    convert (convex_Ioo (-(1 / 2 : ℝ)) (1 / 2)).linear_preimage Complex.reCLM.toLinearMap using 1
  have hDF : DifferentiableOn ℂ F S := by
    intro z hz
    change |z.re| < 1 / 2 at hz
    exact (hF z hz.le).differentiableWithinAt
  have hDG : DifferentiableOn ℂ G S := by
    intro z hz
    change |z.re| < 1 / 2 at hz
    exact (hG z hz.le).differentiableWithinAt
  have hFA : AnalyticOnNhd ℂ F S := hDF.analyticOnNhd hSo
  have hGA : AnalyticOnNhd ℂ G S := hDG.analyticOnNhd hSo
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hn : Tendsto (fun n : ℕ => (r n : ℂ) * I) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp hr
    simpa only [Function.comp_def, Complex.ofReal_zero, zero_mul] using h.mul_const I
  have hclosure : (0 : ℂ) ∈ closure ({z | F z = G z} \ {(0 : ℂ)}) := by
    apply mem_closure_of_tendsto hn
    filter_upwards with n
    refine ⟨haxis (r n), ?_⟩
    simpa only [mem_singleton_iff] using
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (by dsimp [r]; positivity : r n ≠ 0)) I_ne_zero
  have heq : EqOn F G S := hFA.eqOn_of_preconnected_of_mem_closure hGA hSconvex.isPreconnected
    (by norm_num [S]) hclosure
  have hST : S ⊆ T := by
    intro z hz
    change |z.re| < 1 / 2 at hz
    exact hz.le
  have hTS : T ⊆ closure S := by
    intro z hz
    change |z.re| ≤ 1 / 2 at hz
    have hl : Tendsto (fun n : ℕ => ((1 - 1 / (n + 1 : ℝ) : ℝ) : ℂ) * z) atTop (𝓝 z) := by
      have hh : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 - 0 : ℝ)) :=
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simp only [sub_zero] at hh
      simpa only [Function.comp_def, sub_zero, Complex.ofReal_one, one_mul] using
        ((Complex.continuous_ofReal.tendsto 1).comp hh).mul_const z
    apply mem_closure_of_tendsto hl
    filter_upwards with n
    have hn0 : 0 < 1 / (n + 1 : ℝ) := by positivity
    have hn1 : 1 / (n + 1 : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    change |((((1 - 1 / (n + 1 : ℝ) : ℝ) : ℂ) * z)).re| < 1 / 2
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr hn1)]
    have hp := mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr hn1)
    nlinarith
  have hFc : ContinuousOn F T := fun z hz => (hF z hz).continuousAt.continuousWithinAt
  have hGc : ContinuousOn G T := fun z hz => (hG z hz).continuousAt.continuousWithinAt
  exact heq.of_subset_closure hFc hGc hST hTS

end
end ArtinMatthews
