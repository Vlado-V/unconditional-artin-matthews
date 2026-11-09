module

public import ArtinMatthews.SpectralKXDerivativeBounds
public import ArtinMatthews.SpectralKLWindowSynthesisBounds
public import ArtinMatthews.SpectralDerivativeTowerSmooth


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped Topology ContDiff
noncomputable section

def spectralKLWindowSynthesisDerivative (n : ℕ) (h : ℂ → ℂ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then ∫ t in Ioi (0 : ℝ), spectralKXDerivative n ((t : ℂ) * Complex.I) x *
    spectralKLWindowData h g t * (spectralKLPlancherelWeight t : ℂ) else 0

@[simp] theorem spectralKLWindowSynthesisDerivative_zero (h : ℂ → ℂ) (g : ℝ → ℂ) :
    spectralKLWindowSynthesisDerivative 0 h g = spectralKLWindowSynthesis h g := rfl

theorem spectralKXDerivative_order_continuous (n : ℕ) {x : ℝ} (hx : 0 < x) :
    Continuous (fun ν : ℂ => spectralKXDerivative n ν x) := by
  induction n with
  | zero => exact (schlafliBesselK_order_differentiable hx).continuous
  | succ n ih =>
      change Continuous (fun ν : ℂ => -(1 / 2 : ℂ) *
        (spectralKXDerivative n (ν - 1) x + spectralKXDerivative n (ν + 1) x))
      exact ((ih.comp (continuous_id.sub continuous_const)).add
        (ih.comp (continuous_id.add continuous_const))).const_mul _

theorem spectralKLWindowDerivative_integrand_bound (n : ℕ) (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (H : ℝ) (hH : 0 ≤ H) (hh : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ H * (1 + t ^ 2))
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t : ℝ, a ≤ x →
      ‖spectralKXDerivative n ((t : ℂ) * Complex.I) x * spectralKLWindowData h g t *
        (spectralKLPlancherelWeight t : ℂ)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨K, hK, hDK⟩ := spectralKXDerivative_compact_bound n a ha
  obtain ⟨F, hF, hData⟩ := spectralKLWindowData_rapid h g hg hc hp H hH hh (n + 4)
  refine ⟨(2 / Real.pi ^ 2) * K * F * 2 ^ (n + 2), by positivity, ?_⟩
  intro x t hax
  have he : (Real.exp (Real.pi * |t| / 2)) ^ 2 = Real.exp (Real.pi * |t|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hd : (1 + t ^ 2) ^ ((n + 2) + 2) * Real.exp (Real.pi * |t| / 2) *
      ‖spectralKLWindowData h g t‖ ≤ F := by simpa only [Nat.add_assoc] using hData t
  have hk : Real.exp (Real.pi * |t| / 2) * ‖spectralKXDerivative n ((t : ℂ) * Complex.I) x‖ ≤
      K * (1 + |t|) ^ (n + 2) / (1 : ℝ) ^ (n + 2) := by simpa only [one_pow, div_one] using hDK t x hax
  have hb := spectralKLInverseKEnvelope_scalar (n + 2) t 1 (Real.exp (Real.pi * |t| / 2)) K F
    ‖spectralKXDerivative n ((t : ℂ) * Complex.I) x‖ ‖spectralKLWindowData h g t‖ |spectralKLPlancherelWeight t|
    zero_lt_one (Real.exp_pos _) hK.le hF (norm_nonneg _) (norm_nonneg _) (abs_nonneg _)
    hk hd (by rw [he]; exact spectralKLPlancherelWeight_abs_bound t)
  simpa only [one_pow, div_one, norm_mul, Complex.norm_real, Real.norm_eq_abs] using hb

theorem spectralKLWindowDerivative_integrand_continuous (n : ℕ) (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hh : Continuous (fun t : ℝ => h (t : ℂ)))
    (hg : Continuous g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    {x : ℝ} (hx : 0 < x) :
    Continuous (fun t : ℝ => spectralKXDerivative n ((t : ℂ) * Complex.I) x *
      spectralKLWindowData h g t * (spectralKLPlancherelWeight t : ℂ)) :=
  (((spectralKXDerivative_order_continuous n hx).comp (by fun_prop)).mul
    (spectralKLWindowData_continuous h g hh hg hc hp)).mul
      (Complex.continuous_ofReal.comp spectralKLPlancherelWeight_continuous)

theorem spectralKLWindowSynthesisDerivative_hasDerivAt (n : ℕ) (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hh : Continuous (fun t : ℝ => h (t : ℂ)))
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (H : ℝ) (hH : 0 ≤ H) (hbound : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ H * (1 + t ^ 2))
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (spectralKLWindowSynthesisDerivative n h g)
      (spectralKLWindowSynthesisDerivative (n + 1) h g x) x := by
  let K (m : ℕ) (y t : ℝ) := spectralKXDerivative m ((t : ℂ) * Complex.I) y *
    spectralKLWindowData h g t * (spectralKLPlancherelWeight t : ℂ)
  obtain ⟨C, _, hC⟩ := spectralKLWindowDerivative_integrand_bound (n + 1) h g hg hc hp H hH hbound (x / 2) (by linarith)
  obtain ⟨D, _, hD⟩ := spectralKLWindowDerivative_integrand_bound n h g hg hc hp H hH hbound x hx
  have hi : Integrable (K n x) (volume.restrict (Ioi (0 : ℝ))) := by
    apply (integrable_inv_one_add_sq.restrict.const_mul D).mono'
      ((spectralKLWindowDerivative_integrand_continuous n h g hh hg.continuous hc hp hx).aestronglyMeasurable)
    exact ae_of_all _ fun t => by simpa only [K, div_eq_mul_inv] using hD x t le_rfl
  have hr := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := K n) (F' := K (n + 1)) (μ := volume.restrict (Ioi (0 : ℝ)))
    (s := Ioi (x / 2)) (Ioi_mem_nhds (by linarith : x / 2 < x))
    (by
      filter_upwards [eventually_gt_nhds (by linarith : (0 : ℝ) < x)] with y hy
      exact (spectralKLWindowDerivative_integrand_continuous n h g hh hg.continuous hc hp hy).aestronglyMeasurable)
    hi
    ((spectralKLWindowDerivative_integrand_continuous (n + 1) h g hh hg.continuous hc hp hx).aestronglyMeasurable)
    (ae_of_all _ fun t y hy => by simpa only [K, div_eq_mul_inv] using hC y t hy.le)
    (integrable_inv_one_add_sq.restrict.const_mul C)
    (ae_of_all _ fun t y hy =>
      ((spectralKXDerivative_hasDerivAt n ((t : ℂ) * Complex.I) y (by have hy' : x / 2 < y := hy; linarith : 0 < y)).mul_const
        (spectralKLWindowData h g t)).mul_const (spectralKLPlancherelWeight t : ℂ))).2
  have heq : spectralKLWindowSynthesisDerivative n h g =ᶠ[𝓝 x]
      (fun y => ∫ t in Ioi (0 : ℝ), K n y t) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    simp only [spectralKLWindowSynthesisDerivative, ite_eq_left hy, K]
  rw [spectralKLWindowSynthesisDerivative, ite_eq_left hx]
  exact hr.congr_of_eventuallyEq heq

theorem spectralKLWindowSynthesis_contDiffOn (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hh : Continuous (fun t : ℝ => h (t : ℂ)))
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (H : ℝ) (hH : 0 ≤ H) (hbound : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ H * (1 + t ^ 2)) :
    ContDiffOn ℝ ∞ (spectralKLWindowSynthesis h g) (Ioi (0 : ℝ)) := by
  have hhigher := spectral_contDiffOn_of_hasDerivAt_tower
    (fun n => spectralKLWindowSynthesisDerivative n h g) isOpen_Ioi
    (fun n x hx => spectralKLWindowSynthesisDerivative_hasDerivAt n h g hh hg hc hp H hH hbound hx)
  simpa only [spectralKLWindowSynthesisDerivative_zero] using hhigher 0

end
end ArtinMatthews
