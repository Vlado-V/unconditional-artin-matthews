module

public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity


set_option backward.privateInPublic true
@[expose] public section

/-! Smoothness, the chain rule, and the zeroth energy of a compact
logarithmic pullback. -/
namespace ArtinMatthews

open MeasureTheory Set
open scoped ContDiff SchwartzMap

noncomputable section

def sourceMellinLogPullback (χ g : ℝ → ℂ) : ℝ → ℂ :=
  fun u => χ u * g (Real.exp u)

theorem sourceMellinLogPullback_contDiff (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (g : 𝓢(ℝ, ℂ)) : ContDiff ℝ ∞ (sourceMellinLogPullback χ g) :=
  hχ.mul (g.smooth'.comp Real.contDiff_exp)

theorem sourceMellinLogPullback_hasCompactSupport (χ g : ℝ → ℂ) (hc : HasCompactSupport χ) :
    HasCompactSupport (sourceMellinLogPullback χ g) := by
  change HasCompactSupport (χ * (g ∘ Real.exp))
  exact hc.mul_right

theorem sourceMellinLogPullback_deriv (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (g : 𝓢(ℝ, ℂ)) :
    deriv (sourceMellinLogPullback χ g) =
      sourceMellinLogPullback (deriv χ) g +
        sourceMellinLogPullback (fun u => χ u * (Real.exp u : ℂ)) (deriv g) := by
  funext u
  have h₁ := ((hχ.differentiable (by simp)) u).hasDerivAt
  have h₂ := (g.hasDerivAt (Real.exp u)).scomp u (Real.hasDerivAt_exp u)
  change deriv (χ * ((g : ℝ → ℂ) ∘ Real.exp)) u =
    deriv χ u * g (Real.exp u) + (χ u * (Real.exp u : ℂ)) * deriv g (Real.exp u)
  simpa only [Pi.mul_apply, Function.comp_apply, Complex.real_smul, mul_assoc] using
    (h₁.mul h₂).deriv

private theorem compact_iteratedDeriv {f : ℝ → ℂ} (hc : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k f) := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hc
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

theorem sourceMellinLogPullback_derivative_integrable_sq
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) :
    Integrable (fun u => ‖iteratedDeriv k (sourceMellinLogPullback χ g) u‖ ^ 2) := by
  let d := iteratedDeriv k (sourceMellinLogPullback χ g)
  have hd : Continuous d :=
    (sourceMellinLogPullback_contDiff χ hχ g).continuous_iteratedDeriv k (by simp)
  have hs : HasCompactSupport (fun u => ‖d u‖) :=
    (compact_iteratedDeriv (sourceMellinLogPullback_hasCompactSupport χ g hc) k).norm
  have hs₂ : HasCompactSupport (fun u => ‖d u‖ ^ 2) := by
    rw [show (fun u => ‖d u‖ ^ 2) = (fun u => ‖d u‖) * (fun u => ‖d u‖) from
      funext fun u => pow_two _]
    exact hs.mul_right
  exact (hd.norm.pow 2).integrable_of_hasCompactSupport hs₂

theorem sourceMellinLogPullback_zero_energy_on (χ : ℝ → ℂ) (hχ : Continuous χ)
    {a b : ℝ} (hs : tsupport χ ⊆ Icc a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : 𝓢(ℝ, ℂ),
      (∫ u, ‖sourceMellinLogPullback χ g u‖ ^ 2) ≤
        C * ∫ x in Icc (Real.exp a) (Real.exp b), ‖g x‖ ^ 2 := by
  obtain ⟨M,hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hχ.continuousOn
  let A := max M 0
  let C := A^2 / Real.exp a
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hC,fun g => ?_⟩
  let f (u : ℝ) := ‖sourceMellinLogPullback χ g u‖ ^ 2
  let w (u : ℝ) := Real.exp u * ‖g (Real.exp u)‖ ^ 2
  have hf : IntegrableOn f (Icc a b) :=
    ((hχ.mul (g.continuous.comp Real.continuous_exp)).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hw : IntegrableOn w (Icc a b) :=
    (Real.continuous_exp.mul ((g.continuous.comp Real.continuous_exp).norm.pow 2)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hsupport (u : ℝ) (hu : u ∉ Icc a b) : f u = 0 := by
    have hz : χ u = 0 := by
      by_contra hn
      exact hu (hs (subset_closure hn))
    simp [f,sourceMellinLogPullback,hz]
  have hp (u : ℝ) (hu : u ∈ Icc a b) : f u ≤ C * w u := by
    have hχu : ‖χ u‖ ≤ A := (hM u hu).trans (le_max_left _ _)
    have hSq : ‖χ u‖ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hχu 2
    have hExp : A ^ 2 ≤ C * Real.exp u := calc
      _ = C * Real.exp a := (div_mul_cancel₀ _ (Real.exp_ne_zero a)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu.1) hC
    change ‖χ u * g (Real.exp u)‖ ^ 2 ≤ C * (Real.exp u * ‖g (Real.exp u)‖ ^ 2)
    rw [norm_mul, mul_pow]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hSq.trans hExp)
      (sq_nonneg ‖g (Real.exp u)‖)
  have hchange : (∫ u in Icc a b, w u) =
      ∫ x in Icc (Real.exp a) (Real.exp b), ‖g x‖ ^ 2 := by
    rw [← Real.image_exp_Icc]
    symm
    simpa only [w, abs_of_pos (Real.exp_pos _), smul_eq_mul] using
      integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
        (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn
        (fun x : ℝ => ‖g x‖ ^ 2)
  calc
    (∫ u, f u) = ∫ u in Icc a b, f u :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hsupport).symm
    _ ≤ ∫ u in Icc a b, C * w u := setIntegral_mono_on hf (hw.const_mul C) measurableSet_Icc hp
    _ = _ := by rw [integral_const_mul, hchange]

end
end ArtinMatthews
