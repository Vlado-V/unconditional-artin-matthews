module

public import ArtinMatthews.SpectralGamma0EnergyGraph
public import Mathlib.MeasureTheory.Integral.DominatedConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! Dominated convergence in the actual L² norm, with explicit measurable
representatives and a square-integrable majorant. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem spectralL2_norm_sq_integral (u : Lp E 2 μ) :
    ‖u‖^2=∫ x, ‖u x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem spectralL2_toLp_dominated_convergence
    (u : ℕ → α → E) (v : α → E) (hu : ∀ n, MemLp (u n) 2 μ) (hv : MemLp v 2 μ)
    (b : α → ℝ) (hb : MemLp b 2 μ)
    (hub : ∀ n, ∀ᵐ x ∂μ, ‖u n x‖ ≤ b x) (hvb : ∀ᵐ x ∂μ, ‖v x‖ ≤ b x)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (v x))) :
    Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hv.toLp v)) := by
  have hbi : Integrable (fun x => 4*(b x)^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using (hb.integrable_norm_pow (by norm_num)).const_mul 4
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun x => ‖u n x-v x‖^2) μ :=
    (((hu n).aestronglyMeasurable.sub hv.aestronglyMeasurable).norm.aemeasurable.pow_const 2).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖‖u n x-v x‖^2‖ ≤ 4*(b x)^2 := by
    filter_upwards [hub n,hvb] with x hux hvx
    have hbx : 0 ≤ b x := (norm_nonneg _).trans hvx
    have hd : ‖u n x-v x‖ ≤ 2*b x := (norm_sub_le _ _).trans (by linarith)
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have hsquare : ‖u n x-v x‖^2 ≤ (2*b x)^2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hd
    nlinarith
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => ‖u n x-v x‖^2) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [ht] with x hx
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using
      ((hx.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => v x) atTop (𝓝 (v x)))).norm.pow 2)
  have hsum : Tendsto (fun n => ∫ x, ‖u n x-v x‖^2 ∂μ) atTop (𝓝 (0:ℝ)) := by
    have h := tendsto_integral_of_dominated_convergence (F := fun n x => ‖u n x-v x‖^2)
      (f := fun _ => (0:ℝ)) (fun x => 4*(b x)^2) hmeas hbi hbound hlim
    simpa only [integral_zero] using h
  have he (n : ℕ) : ‖(hu n).toLp (u n)-hv.toLp v‖^2=
      ∫ x, ‖u n x-v x‖^2 ∂μ := by
    rw [spectralL2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hu n).toLp (u n)) (hv.toLp v),
      (hu n).coeFn_toLp,hv.coeFn_toLp] with x hs hx hy
    rw [hs]
    simp only [Pi.sub_apply]
    rw [hx,hy]
  have hnorm : Tendsto (fun n => ‖(hu n).toLp (u n)-hv.toLp v‖) atTop (𝓝 (0:ℝ)) := by
    have hsq : Tendsto (fun n => ‖(hu n).toLp (u n)-hv.toLp v‖^2) atTop (𝓝 (0:ℝ)) :=
      hsum.congr (fun n => (he n).symm)
    have hr := (Real.continuous_sqrt.tendsto (0:ℝ)).comp hsq
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hr
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [dist_eq_norm] using hnorm

end ArtinMatthews
