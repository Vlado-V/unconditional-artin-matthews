module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Topology.ContinuousMap.Compact


set_option backward.privateInPublic true
@[expose] public section

/-!
# Compact ContinuousMap-valued complex differentiation

A continuous family of pointwise derivatives controls the difference quotient uniformly
on a compact parameter space through the scalar mean value inequality.
-/

open Filter Topology

namespace ArtinMatthews

/-- Pointwise complex derivatives upgrade to a derivative in the uniform norm when the
family of derivatives is continuous in that norm. -/
theorem hasDerivAt_continuousMap_of_pointwise
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (F G : ℂ → C(X, ℂ)) (hG : Continuous G)
    (hderiv : ∀ z x, HasDerivAt (fun w => F w x) (G z x) z) (z : ℂ) :
    HasDerivAt F (G z) z := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hGδ⟩ := Metric.continuousAt_iff.mp hG.continuousAt ε hε
  filter_upwards [Metric.ball_mem_nhds z hδ] with w hw
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro x
  have hpoint : ∀ u ∈ Metric.ball z δ, ‖G u x - G z x‖ ≤ ε := by
    intro u hu
    exact ((G u - G z).norm_coe_le_norm x).trans
      (le_of_lt (by simpa only [dist_eq_norm] using hGδ hu))
  have hscalar : ∀ u ∈ Metric.ball z δ,
      HasDerivWithinAt (fun v => F v x - F z x - (v - z) * G z x)
        (G u x - G z x) (Metric.ball z δ) u := by
    intro u _
    convert! (((hderiv u x).sub_const (F z x)).fun_sub
      (((hasDerivAt_id' u).sub_const z).mul_const (G z x))).hasDerivWithinAt using 1
    simp only [one_mul]
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hscalar hpoint (convex_ball z δ) (Metric.mem_ball_self hδ) hw
  simpa only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
    sub_self, zero_mul, sub_zero] using hbound

/-- Joint continuity of the evaluated derivatives is sufficient for differentiation
in the uniform norm. -/
theorem hasDerivAt_continuousMap_of_jointlyContinuous
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (F G : ℂ → C(X, ℂ))
    (hG : Continuous (fun p : ℂ × X => G p.1 p.2))
    (hderiv : ∀ z x, HasDerivAt (fun w => F w x) (G z x) z) (z : ℂ) :
    HasDerivAt F (G z) z :=
  hasDerivAt_continuousMap_of_pointwise F G
    (ContinuousMap.continuous_of_continuous_uncurry G hG) hderiv z

end ArtinMatthews
