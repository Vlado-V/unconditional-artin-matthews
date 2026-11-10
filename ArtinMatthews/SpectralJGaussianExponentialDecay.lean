module

public import ArtinMatthews.SpectralJGaussianSquaredKernel
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


set_option backward.privateInPublic true
@[expose] public section

/-! In the squared coordinate the genuine exponential error controls both
boundary terms and the (L^1) mass of the transferred test. -/

namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section

private def linearExpWeight (s : ℝ) : ℝ := (1 + s) * Real.exp (-s)

private theorem linearExpWeight_integrable : IntegrableOn linearExpWeight (Ioi (0 : ℝ)) := by
  have h₀ : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Ioi (0 : ℝ)) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0
  have h₁ : IntegrableOn (fun s : ℝ => s * Real.exp (-s)) (Ioi (0 : ℝ)) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := 1) (by norm_num) (by norm_num)
  convert h₀.add h₁ using 1
  funext s
  simp only [linearExpWeight, Pi.add_apply]
  ring

private theorem exp_le_linearExpWeight {s : ℝ} (hs : 0 < s) :
    Real.exp (-s) ≤ linearExpWeight s := by
  unfold linearExpWeight
  nlinarith [mul_nonneg hs.le (Real.exp_nonneg (-s))]

private theorem mul_exp_le_linearExpWeight (s : ℝ) :
    s * Real.exp (-s) ≤ linearExpWeight s := by
  unfold linearExpWeight
  nlinarith [Real.exp_nonneg (-s)]

private theorem integrableOn_of_expLinear_bound {u : ℝ → ℂ}
    (hu : ContinuousOn u (Ioi (0 : ℝ))) (B : ℝ)
    (h : ∀ s : ℝ, 0 < s → ‖u s‖ ≤ B * linearExpWeight s) :
    IntegrableOn u (Ioi (0 : ℝ)) := by
  apply (linearExpWeight_integrable.const_mul B).mono'
    (hu.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact h s hs

private theorem boundary_zero_of_mul_exp_bound {u : ℝ → ℂ} (B : ℝ)
    (h : ∀ s : ℝ, 0 < s → ‖u s‖ ≤ B * (s * Real.exp (-s))) :
    Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 0) ∧ Tendsto u atTop (𝓝 0) := by
  have hc : Continuous (fun s : ℝ => B * (s * Real.exp (-s))) := by fun_prop
  have hzero : Tendsto (fun s : ℝ => B * (s * Real.exp (-s))) (𝓝[>] 0) (𝓝 0) := by
    have hn : ContinuousWithinAt (fun s : ℝ => B * (s * Real.exp (-s))) (Ioi 0) (0 : ℝ) :=
      hc.continuousAt.continuousWithinAt
    simpa only [zero_mul, mul_zero] using hn.tendsto
  have htop : Tendsto (fun s : ℝ => B * (s * Real.exp (-s))) atTop (𝓝 0) := by
    have hB : Tendsto (fun _ : ℝ => B) atTop (𝓝 B) := tendsto_const_nhds
    have ht := hB.mul (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
    simpa only [pow_one, mul_zero] using ht
  have hp : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  exact ⟨squeeze_zero_norm' (hp.mono h) hzero,
    squeeze_zero_norm' ((eventually_gt_atTop (0 : ℝ)).mono h) htop⟩

private def squareProfileFlux (g : ℝ → ℂ) (s : ℝ) : ℂ := (s : ℂ) * deriv g s

private theorem squareProfileFlux_hasDerivAt {g : ℝ → ℂ} {s : ℝ}
    (hg : ContDiffOn ℝ 1 (deriv g) (Ioi (0 : ℝ))) (hs : 0 < s) :
    HasDerivAt (squareProfileFlux g) (deriv g s + (s : ℂ) * deriv (deriv g) s) s := by
  have hd := ((hg s hs).contDiffAt (Ioi_mem_nhds hs)).differentiableAt (by norm_num)
  have h := ((hasDerivAt_id' s).ofReal_comp).fun_mul hd.hasDerivAt
  change HasDerivAt (fun q : ℝ => (q : ℂ) * deriv g q) _ s
  simpa only [Complex.ofReal_one, one_mul] using h

private theorem squareProfileFlux_deriv_bound {g : ℝ → ℂ}
    (hg : ContDiffOn ℝ 1 (deriv g) (Ioi (0 : ℝ))) (E : ℝ)
    (h₁ : ∀ s : ℝ, 0 < s → ‖deriv g s‖ ≤ E * Real.exp (-s))
    (h₂ : ∀ s : ℝ, 0 < s → ‖deriv (deriv g) s‖ ≤ E * Real.exp (-s))
    (s : ℝ) (hs : 0 < s) :
    ‖deriv (squareProfileFlux g) s‖ ≤ E * linearExpWeight s := by
  rw [(squareProfileFlux_hasDerivAt hg hs).deriv]
  calc
    _ ≤ ‖deriv g s‖ + ‖(s : ℂ) * deriv (deriv g) s‖ := norm_add_le _ _
    _ ≤ E * Real.exp (-s) + s * (E * Real.exp (-s)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
      exact add_le_add (h₁ s hs) (mul_le_mul_of_nonneg_left (h₂ s hs) hs.le)
    _ = _ := by unfold linearExpWeight; ring

private theorem mul_norm_le_of_bounds {z₁ z₂ : ℂ} {B₁ B₂ : ℝ}
    (h₁ : ‖z₁‖ ≤ B₁) (h₂ : ‖z₂‖ ≤ B₂) : ‖z₁ * z₂‖ ≤ B₁ * B₂ := by
  rw [norm_mul]
  exact mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)

/-- Exact radial transfer on the positive ray for an exponentially bounded
(C^2) profile. The boundary terms vanish at both ends. -/
theorem spectralJGaussianSquared_integral_adjoint_of_exp (g : ℝ → ℂ)
    (hg : ContDiffOn ℝ 2 g (Ioi (0 : ℝ))) (E : ℝ) (hE : 0 ≤ E)
    (h₀ : ∀ s : ℝ, 0 < s → ‖g s‖ ≤ E * Real.exp (-s))
    (h₁ : ∀ s : ℝ, 0 < s → ‖deriv g s‖ ≤ E * Real.exp (-s))
    (h₂ : ∀ s : ℝ, 0 < s → ‖deriv (deriv g) s‖ ≤ E * Real.exp (-s))
    (w : ℝ) (hw : 0 < w) :
    (∫ s in Ioi (0 : ℝ), g s * spectralJGaussianSquaredKernel w s) =
      (-(8 : ℂ) / (w : ℂ)) *
        ∫ s in Ioi (0 : ℝ), deriv (fun q : ℝ => (q : ℂ) * deriv g q) s *
          spectralJGaussianSquaredKernel w s := by
  obtain ⟨C, hC, hQ, hQd⟩ := spectralJGaussianSquaredKernel_bounds
  let Q := spectralJGaussianSquaredKernel w
  let c : ℂ := ((-(w / 8) : ℝ) : ℂ)
  let D : ℝ := (w / 8) * C
  let v := fun s : ℝ => (s : ℂ) * deriv Q s
  let b := squareProfileFlux g
  have hg₁ : ContDiffOn ℝ 1 (deriv g) (Ioi (0 : ℝ)) := hg.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hb₁ : ContDiffOn ℝ 1 b (Ioi (0 : ℝ)) :=
    Complex.ofRealCLM.contDiff.contDiffOn.mul hg₁
  have hb₂ : ContinuousOn (deriv b) (Ioi (0 : ℝ)) :=
    (hb₁.deriv_of_isOpen (m := 0) isOpen_Ioi (by norm_num)).continuousOn
  have hdg (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : HasDerivAt g (deriv g s) s :=
    (((hg s hs).contDiffAt (Ioi_mem_nhds hs)).differentiableAt (by norm_num)).hasDerivAt
  have hdb (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : HasDerivAt b (deriv b s) s :=
    (((hb₁ s hs).contDiffAt (Ioi_mem_nhds hs)).differentiableAt (by norm_num)).hasDerivAt
  have hQdiff : Differentiable ℝ Q := spectralJGaussianSquaredKernel_differentiable w
  have hQc : Continuous Q := hQdiff.continuous
  have hQdc : Continuous (deriv Q) := spectralJGaussianSquaredKernel_deriv_continuous w
  have hcv : Continuous (fun s => c * Q s) := continuous_const.mul hQc
  have hcNorm : ‖c‖ = w / 8 := by
    dsimp only [c]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
  have hcQ (s : ℝ) (hs : 0 < s) : ‖c * Q s‖ ≤ D := by
    rw [norm_mul, hcNorm]
    exact mul_le_mul_of_nonneg_left (hQ w s hw.le hs.le) (by positivity)
  have hvBound (s : ℝ) (hs : 0 < s) : ‖v s‖ ≤ s * D := by
    dsimp only [v]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left (hQd w s hw.le hs) hs.le
  have hbBound (s : ℝ) (hs : 0 < s) : ‖b s‖ ≤ E * (s * Real.exp (-s)) := by
    dsimp only [b, squareProfileFlux]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    calc
      _ ≤ s * (E * Real.exp (-s)) := mul_le_mul_of_nonneg_left (h₁ s hs) hs.le
      _ = _ := by ring
  have hcomm : deriv g * v = b * deriv Q := by
    funext s
    simp only [Pi.mul_apply, v, b, squareProfileFlux]
    ring
  have hi₁ : IntegrableOn (g * fun s => c * Q s) (Ioi (0 : ℝ)) := by
    apply integrableOn_of_expLinear_bound (hg.continuousOn.mul hcv.continuousOn) (E * D)
    intro s hs
    calc
      _ ≤ (E * Real.exp (-s)) * D := mul_norm_le_of_bounds (h₀ s hs) (hcQ s hs)
      _ = (E * D) * Real.exp (-s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_linearExpWeight hs) (by positivity)
  have hi₂ : IntegrableOn (b * deriv Q) (Ioi (0 : ℝ)) := by
    apply integrableOn_of_expLinear_bound (hb₁.continuousOn.mul hQdc.continuousOn) (E * D)
    intro s hs
    calc
      _ ≤ (E * (s * Real.exp (-s))) * D := mul_norm_le_of_bounds (hbBound s hs) (hQd w s hw.le hs)
      _ = (E * D) * (s * Real.exp (-s)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_exp_le_linearExpWeight s) (by positivity)
  have hi₂' : IntegrableOn (deriv g * v) (Ioi (0 : ℝ)) := by rw [hcomm]; exact hi₂
  have hi₃ : IntegrableOn (deriv b * Q) (Ioi (0 : ℝ)) := by
    apply integrableOn_of_expLinear_bound (hb₂.mul hQc.continuousOn) (E * C)
    intro s hs
    calc
      _ ≤ (E * linearExpWeight s) * C :=
        mul_norm_le_of_bounds (squareProfileFlux_deriv_bound hg₁ E h₁ h₂ s hs) (hQ w s hw.le hs.le)
      _ = _ := by ring
  have hbd₁ := boundary_zero_of_mul_exp_bound (u := g * v) (E * D) (fun s hs => by
    calc
      _ ≤ (E * Real.exp (-s)) * (s * D) := mul_norm_le_of_bounds (h₀ s hs) (hvBound s hs)
      _ = _ := by ring)
  have hbd₂ := boundary_zero_of_mul_exp_bound (u := b * Q) (E * C) (fun s hs => by
    calc
      _ ≤ (E * (s * Real.exp (-s))) * C := mul_norm_le_of_bounds (hbBound s hs) (hQ w s hw.le hs.le)
      _ = _ := by ring)
  have hibp₁ := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := g) (u' := deriv g) (v := v) (v' := fun s => c * Q s)
    hdg (fun s _ => spectralJGaussianSquaredKernel_flux_hasDerivAt w s)
    hi₁ hi₂' hbd₁.1 hbd₁.2
  have hibp₂ := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := b) (u' := deriv b) (v := Q) (v' := deriv Q)
    hdb (fun s _ => (hQdiff s).hasDerivAt) hi₂ hi₃ hbd₂.1 hbd₂.2
  have hrel : c * (∫ s in Ioi (0 : ℝ), g s * Q s) =
      ∫ s in Ioi (0 : ℝ), deriv b s * Q s := by
    rw [← integral_const_mul]
    calc
      _ = ∫ s in Ioi (0 : ℝ), g s * (c * Q s) := by
        apply integral_congr_ae
        filter_upwards with s
        ring
      _ = -(∫ s in Ioi (0 : ℝ), deriv g s * v s) := by
        simpa only [sub_self, zero_sub] using hibp₁
      _ = -(∫ s in Ioi (0 : ℝ), b s * deriv Q s) := by
        change -(∫ s in Ioi (0 : ℝ), (deriv g * v) s) =
          -(∫ s in Ioi (0 : ℝ), (b * deriv Q) s)
        rw [hcomm]
      _ = _ := by
        rw [hibp₂]
        simp
  have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hcInv : (-(8 : ℂ) / (w : ℂ)) * c = 1 := by
    dsimp only [c]
    push_cast
    field_simp
  change (∫ s in Ioi (0 : ℝ), g s * Q s) =
    (-(8 : ℂ) / (w : ℂ)) * ∫ s in Ioi (0 : ℝ), deriv b s * Q s
  rw [← hrel, ← mul_assoc, hcInv, one_mul]

/-- The constant in the (1/w) tail estimate is proportional to the given
exponential error, uniformly in the approximating profile. -/
theorem spectralJGaussianSquared_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℂ) (_ : ContDiffOn ℝ 2 g (Ioi (0 : ℝ)))
      (E : ℝ), 0 ≤ E →
      (∀ s : ℝ, 0 < s → ‖g s‖ ≤ E * Real.exp (-s)) →
      (∀ s : ℝ, 0 < s → ‖deriv g s‖ ≤ E * Real.exp (-s)) →
      (∀ s : ℝ, 0 < s → ‖deriv (deriv g) s‖ ≤ E * Real.exp (-s)) →
      ∀ w : ℝ, 0 < w →
        ‖∫ s in Ioi (0 : ℝ), g s * spectralJGaussianKernel (Real.sqrt s) w‖ ≤ C * E / w := by
  obtain ⟨C, hC, hQ, _⟩ := spectralJGaussianSquaredKernel_bounds
  let M := ∫ s in Ioi (0 : ℝ), linearExpWeight s
  have hM : 0 ≤ M := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : 0 ≤ s := (mem_Ioi.mp hs).le
    unfold linearExpWeight
    positivity
  refine ⟨8 * C * (M + 1), by positivity, ?_⟩
  intro g hg E hE h₀ h₁ h₂ w hw
  have heq : (∫ s in Ioi (0 : ℝ), g s * spectralJGaussianKernel (Real.sqrt s) w) =
      ∫ s in Ioi (0 : ℝ), g s * spectralJGaussianSquaredKernel w s := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [spectralJGaussianSquaredKernel_eq_gaussianKernel w s hw.le (mem_Ioi.mp hs).le]
  rw [heq, spectralJGaussianSquared_integral_adjoint_of_exp g hg E hE h₀ h₁ h₂ w hw]
  have hg₁ : ContDiffOn ℝ 1 (deriv g) (Ioi (0 : ℝ)) := hg.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hmass : ‖∫ s in Ioi (0 : ℝ), deriv (squareProfileFlux g) s *
        spectralJGaussianSquaredKernel w s‖ ≤ (E * C) * M := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (linearExpWeight_integrable.const_mul (E * C))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : 0 < s := mem_Ioi.mp hs
    calc
      _ ≤ (E * linearExpWeight s) * C :=
        mul_norm_le_of_bounds (squareProfileFlux_deriv_bound hg₁ E h₁ h₂ s hs') (hQ w s hw.le hs'.le)
      _ = _ := by ring
  change ‖(-(8 : ℂ) / (w : ℂ)) * ∫ s in Ioi (0 : ℝ), deriv (squareProfileFlux g) s *
    spectralJGaussianSquaredKernel w s‖ ≤ _
  rw [norm_mul, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
  have h8 : ‖(8 : ℂ)‖ = 8 := by norm_num
  rw [h8]
  calc
    _ ≤ (8 / w) * ((E * C) * M) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (8 * C * M) * E / w := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : M ≤ M + 1) (by positivity)) hE) hw.le

end
end ArtinMatthews
