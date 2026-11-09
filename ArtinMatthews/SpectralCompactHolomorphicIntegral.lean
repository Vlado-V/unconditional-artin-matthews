module

public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Tactic.Linarith


set_option backward.privateInPublic true
@[expose] public section

/-! Holomorphic compact integrals. Joint continuity gives local uniform
Cauchy bounds, and difference quotients give measurability of the derivative. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace ArtinMatthews

theorem spectral_hasDerivAt_compact_holomorphic_integral
    {K : Set ℝ} (hK : IsCompact K) {F : ℂ → ℝ → ℂ}
    (hF : ContinuousOn (fun p : ℂ × ℝ => F p.1 p.2) (univ ×ˢ K))
    (hHol : ∀ x ∈ K, Differentiable ℂ (fun z => F z x)) (z₀ : ℂ) :
    HasDerivAt (fun z => ∫ x in K, F z x)
      (∫ x in K, deriv (fun z => F z x) z₀) z₀ := by
  let μ : Measure ℝ := volume.restrict K
  have hKm := hK.isClosed.measurableSet
  letI : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
  have hSlice (z : ℂ) : ContinuousOn (F z) K := hF.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨mem_univ _,hx⟩)
  have hm (z : ℂ) : AEStronglyMeasurable (F z) μ := (hSlice z).aestronglyMeasurable hKm
  have hi : Integrable (F z₀) μ := (hSlice z₀).integrableOn_compact hK
  let δ (n : ℕ) : ℂ := 1/((n : ℂ)+1)
  have hδ : Tendsto δ atTop (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall ?_⟩
    intro n
    change δ n ≠ 0
    exact div_ne_zero one_ne_zero (by exact_mod_cast n.succ_ne_zero)
  let F' (z : ℂ) (x : ℝ) := deriv (fun w => F w x) z
  have hm' : AEStronglyMeasurable (F' z₀) μ := by
    let Q (n : ℕ) (x : ℝ) := (δ n)⁻¹*(F (z₀+δ n) x-F z₀ x)
    apply aestronglyMeasurable_of_tendsto_ae (f := Q) atTop
    · intro n
      exact (continuousOn_const.mul ((hSlice (z₀+δ n)).sub (hSlice z₀))).aestronglyMeasurable hKm
    · filter_upwards [ae_restrict_mem hKm] with x hx
      simpa only [Q, F', smul_eq_mul, Function.comp_def] using
        ((hHol x hx z₀).hasDerivAt.tendsto_slope_zero.comp hδ)
  have hC : IsCompact (Metric.closedBall z₀ 2 ×ˢ K) := (isCompact_closedBall _ _).prod hK
  obtain ⟨M,hM⟩ := hC.exists_bound_of_continuousOn
    (hF.mono (Set.prod_mono (subset_univ _) (Subset.rfl)))
  let R := max M 0
  have hR (z : ℂ) (hz : z ∈ Metric.closedBall z₀ 2) (x : ℝ) (hx : x ∈ K) :
      ‖F z x‖ ≤ R := (hM (z,x) ⟨hz,hx⟩).trans (le_max_left _ _)
  have hb (x : ℝ) (hx : x ∈ K) (z : ℂ) (hz : z ∈ Metric.ball z₀ 1) : ‖F' z x‖ ≤ 2*R := by
    have hz' : z ∈ Metric.closedBall z₀ 2 := Metric.mem_closedBall.mpr (by
      have h := Metric.mem_ball.mp hz
      linarith)
    have hMaps : MapsTo (fun w => F w x) (Metric.ball z 1) (Metric.closedBall (F z x) (2*R)) := by
      intro w hw
      have hw' : w ∈ Metric.closedBall z₀ 2 := Metric.mem_closedBall.mpr (by
        have ht := dist_triangle w z z₀
        have h₁ := Metric.mem_ball.mp hw
        have h₂ := Metric.mem_ball.mp hz
        linarith)
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith only [hR w hw' x hx, hR z hz' x hx])
    simpa only [F', div_one] using
      Complex.norm_deriv_le_div_of_mapsTo_ball (hHol x hx).differentiableOn hMaps one_pos
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (s := Metric.ball z₀ 1) (bound := fun _ => 2*R)
    (Metric.ball_mem_nhds _ one_pos) (Eventually.of_forall hm) hi hm'
    (by filter_upwards [ae_restrict_mem hKm] with x hx; exact hb x hx)
    (integrable_const _) (by
      filter_upwards [ae_restrict_mem hKm] with x hx
      intro z _
      exact (hHol x hx z).hasDerivAt)).2

end ArtinMatthews
