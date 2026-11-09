module

public import ArtinMatthews.SpectralKLCompactOrder
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter Complex
open scoped ContDiff Topology
noncomputable section

/-- The literal Laplace integral of a compact real-variable test. -/
def spectralCompactLaplace (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-(x : ℂ)*z)*g x

theorem spectralCompactLaplace_integrable (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (z : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (-(x : ℂ)*z)*g x) := by
  have hu : Continuous (fun x : ℝ => Complex.exp (-(x : ℂ)*z)) := by fun_prop
  exact (hu.mul hg).integrable_of_hasCompactSupport hc.mul_left

theorem spectralCompactLaplace_hasDerivAt (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (z : ℂ) :
    HasDerivAt (spectralCompactLaplace g)
      (spectralCompactLaplace (fun x : ℝ => -(x : ℂ)*g x) z) z := by
  let F (w : ℂ) (x : ℝ) := Complex.exp (-(x : ℂ)*w)*g x
  let F' (w : ℂ) (x : ℝ) := Complex.exp (-(x : ℂ)*w)*(-(x : ℂ)*g x)
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun x : ℝ => x) (tsupport g))
  let D := max B 1
  have hD : 0 ≤ D := zero_le_one.trans (le_max_right _ _)
  let C := Real.exp (D*(‖z‖+1))*D
  have hderiv (x : ℝ) (w : ℂ) : HasDerivAt (fun v => F v x) (F' w x) w := by
    have h := (((hasDerivAt_id w).const_mul (-(x : ℂ))).cexp).mul_const (g x)
    simpa only [F,F',id_eq,mul_one,mul_assoc] using h
  have hbound (x : ℝ) (w : ℂ) (hw : w ∈ Metric.ball z 1) : ‖F' w x‖ ≤ C*‖g x‖ := by
    by_cases hx : g x = 0
    · simp [F',hx]
    · have hxb : ‖(x : ℂ)‖ ≤ D := by
        rw [Complex.norm_real]
        exact (hB x (subset_tsupport g hx)).trans (le_max_left _ _)
      have hwb : ‖w‖ ≤ ‖z‖+1 := by
        have hw' : ‖w-z‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hw
        calc
          _ = ‖(w-z)+z‖ := by rw [sub_add_cancel]
          _ ≤ ‖w-z‖+‖z‖ := norm_add_le _ _
          _ ≤ _ := by linarith
      have hE : ‖Complex.exp (-(x : ℂ)*w)‖ ≤ Real.exp (D*(‖z‖+1)) := by
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ ‖-(x : ℂ)*w‖ := Complex.re_le_norm _
          _ = ‖(x : ℂ)‖*‖w‖ := by rw [norm_mul,norm_neg]
          _ ≤ _ := mul_le_mul hxb hwb (norm_nonneg _) hD
      dsimp only [F',C]
      rw [norm_mul,norm_mul,norm_neg]
      exact (mul_le_mul hE (mul_le_mul_of_nonneg_right hxb (norm_nonneg _))
        (by positivity) (by positivity)).trans_eq (by ring)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (μ := volume) (s := Metric.ball z 1) (Metric.ball_mem_nhds z (by norm_num))
    (Eventually.of_forall fun w => (spectralCompactLaplace_integrable g hg hc w).aestronglyMeasurable)
    (spectralCompactLaplace_integrable g hg hc z)
    (show Continuous (F' z) from by
      dsimp only [F']
      exact (by fun_prop : Continuous (fun x : ℝ => Complex.exp (-(x : ℂ)*z))).mul
        ((by fun_prop : Continuous (fun x : ℝ => -(x : ℂ))).mul hg)).aestronglyMeasurable
    (ae_of_all _ hbound) ((hg.norm.integrable_of_hasCompactSupport (hc.comp_left (g := norm) (by simp))).const_mul C)
    (ae_of_all _ fun x w _ => hderiv x w)).2

theorem spectralCompactLaplace_entire (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) : Differentiable ℂ (spectralCompactLaplace g) :=
  fun z => (spectralCompactLaplace_hasDerivAt g hg hc z).differentiableAt

theorem spectralCompactLaplace_deriv (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (z : ℂ) :
    spectralCompactLaplace (deriv g) z = z*spectralCompactLaplace g z := by
  let u : ℝ → ℂ := fun x => Complex.exp (-(x : ℂ)*z)
  let u' : ℝ → ℂ := fun x => (-z)*u x
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    have hEmb : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
      exact Complex.ofRealCLM.hasDerivAt
    have h := (hEmb.const_mul (-z)).cexp
    convert h using 1 <;> simp [u,u',mul_comm]
  have hg' := (contDiff_infty_iff_deriv.mp hg).2
  have i0 : Integrable (u*g) := spectralCompactLaplace_integrable g hg.continuous hc z
  have i1 : Integrable (u*deriv g) := spectralCompactLaplace_integrable (deriv g) hg'.continuous hc.deriv z
  have i2 : Integrable (u'*g) := by
    change Integrable (fun x : ℝ => ((-z)*u x)*g x)
    simpa only [mul_assoc,Pi.mul_apply] using i0.const_mul (-z)
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hu x) (fun x _ => (hg.differentiable (by norm_num) x).hasDerivAt) i1 i2 i0
  change (∫ x : ℝ, u x*deriv g x) = -∫ x : ℝ, ((-z)*u x)*g x at h
  simp only [mul_assoc,integral_const_mul] at h
  rw [neg_mul,neg_neg] at h
  exact h

theorem spectralCompactLaplace_iteratedDeriv (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (N : ℕ) (z : ℂ) :
    spectralCompactLaplace (iteratedDeriv N g) z = z^N*spectralCompactLaplace g z := by
  induction N generalizing g with
  | zero => simp
  | succ N ih =>
    rw [iteratedDeriv_succ',ih (deriv g) (contDiff_infty_iff_deriv.mp hg).2 hc.deriv,
      spectralCompactLaplace_deriv g hg hc,pow_succ,mul_assoc]

theorem spectralCompactLaplace_norm_le (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ici (0 : ℝ))
    {z : ℂ} (hz : 0 ≤ z.re) : ‖spectralCompactLaplace g z‖ ≤ ∫ x : ℝ, ‖g x‖ := by
  have hi : Integrable (fun x : ℝ => ‖g x‖) :=
    (hg.integrable_of_hasCompactSupport hc).norm
  apply norm_integral_le_of_norm_le hi
  filter_upwards with x
  by_cases hx : g x = 0
  · simp [hx]
  · have hx0 : 0 ≤ x := hp (subset_tsupport g hx)
    rw [norm_mul,Complex.norm_exp]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [neg_mul,Complex.neg_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hx0 hz))

end
end ArtinMatthews
