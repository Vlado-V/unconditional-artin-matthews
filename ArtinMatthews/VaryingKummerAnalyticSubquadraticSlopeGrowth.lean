module

public import ArtinMatthews.VaryingKummerAnalyticGrowth
public import Mathlib.Analysis.Calculus.DSlope


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine permanence property of subquadratic growth under divided
slopes. The compact neighborhood of the removable singularity is controlled
by continuity; outside it the denominator is bounded away from zero. -/
namespace ArtinMatthews.ReusedGrowth
open Set Filter
open scoped Topology
noncomputable section

theorem HasSubquadraticGrowth.of_norm_le_add_const {f g : ℂ → ℂ}
    (hf : HasSubquadraticGrowth f) (C : ℝ)
    (hb : ∀ z, ‖g z‖ ≤ ‖f z‖ + C) : HasSubquadraticGrowth g := by
  intro ε hε
  have he : 0 < ε/2 := by positivity
  filter_upwards [hf (ε/2) he,eventually_const_le_exp_quad he C,
    eventually_const_le_exp_quad he 2] with R hR hC h2
  intro z hz
  calc
    ‖g z‖ ≤ Real.exp (ε/2*R^2) + Real.exp (ε/2*R^2) :=
      (hb z).trans (add_le_add (hR z hz) hC)
    _ ≤ Real.exp (ε/2*R^2) * Real.exp (ε/2*R^2) := by
      nlinarith [Real.exp_pos (ε/2*R^2)]
    _ = Real.exp (ε*R^2) := by rw [← Real.exp_add]; congr 1; ring

theorem HasSubquadraticGrowth.dslope {f : ℂ → ℂ}
    (hf : HasSubquadraticGrowth f) (hcont : Continuous f) (a : ℂ)
    (hdiff : DifferentiableAt ℂ f a) : HasSubquadraticGrowth (_root_.dslope f a) := by
  have hd : Continuous (_root_.dslope f a) := by
    rw [← continuousOn_univ]
    exact (continuousOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 a)).mpr
      ⟨hcont.continuousOn,hdiff⟩
  obtain ⟨B,hB⟩ := (isCompact_closedBall a 1).exists_bound_of_continuousOn hd.continuousOn
  apply hf.of_norm_le_add_const (‖f a‖ + max B 0)
  intro z
  by_cases hz : dist z a ≤ 1
  · have H := hB z (show z ∈ Metric.closedBall a 1 from hz)
    linarith [norm_nonneg (f z),norm_nonneg (f a),le_max_left B 0]
  · have hh : 1 < ‖z-a‖ := by simpa only [dist_eq_norm] using lt_of_not_ge hz
    have hza : z ≠ a := by intro h; subst z; norm_num at hh
    rw [dslope_of_ne f hza,slope_def_field,norm_div]
    calc
      _ ≤ ‖f z-f a‖ := div_le_self (norm_nonneg _) hh.le
      _ ≤ ‖f z‖+‖f a‖ := norm_sub_le _ _
      _ ≤ ‖f z‖+(‖f a‖+max B 0) := by linarith [le_max_right B 0]

end
end ArtinMatthews.ReusedGrowth
