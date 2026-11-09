module

public import ArtinMatthews.ShiftedSourceBessel


set_option backward.privateInPublic true
@[expose] public section

/-!
# Uniform log separation for families of transformed sources

This uses the existing OAI positive-log Fourier inversion and explicit moment
bound. The quantitative constant is chosen before the kernel F, exposing the
uniformity already present in the lower-level source theorem. No Fourier or
Mellin inversion identity is assumed.
-/

noncomputable section
open Complex MeasureTheory Set OAI
open OAI.LocalLogFourier
open scoped ContDiff FourierTransform SchwartzMap

namespace ArtinMatthews

/-- The existing explicit OAI Fourier bound is uniform over every smooth
positive-axis kernel with the same finite Euler-derivative bounds. -/
theorem coupled_log_separation_uniform_family
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (a M : ι → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) (CF : ℝ) (hCF : 0 ≤ CF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : ℝ → ℂ), ContDiffOn ℝ ∞ F (Ioi 0) →
      (∀ i ≤ J+(volume : Measure ℝ).integrablePower, ∀ x : ℝ, 0 < x →
        (1+x)^A * ‖eulerDeriv F i x‖ ≤ CF) →
      ∀ R : ℝ, 0 < R → ∃ b : SchwartzMap ℝ ℂ,
        (∀ y : ι → ℝ, (∏ j : ι, W j (y j)) * F (R*Real.exp (∑ j : ι, a j*y j)) =
          ∫ t : ℝ, (∏ j : ι, W j (y j) * FourierBridge.logPhase t (a j*y j)) * b t) ∧
        (1+R)^A * (∫ t : ℝ, (1+‖t‖)^J * ‖b t‖) ≤ C := by
  classical
  let T : ℝ := ∑ j : ι, |a j| * M j
  have hT : 0 ≤ T := by dsimp [T]; exact Finset.sum_nonneg (fun j _ ↦ mul_nonneg (abs_nonneg _) (hM j))
  let K : ℕ := J+(volume : Measure ℝ).integrablePower
  let Lwin : ℝ := T+1
  let m : ℝ := Real.exp (-Lwin)
  have hL : 0 ≤ Lwin := by dsimp [Lwin]; linarith
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    simpa using Real.exp_le_exp.mpr (show -Lwin ≤ 0 by linarith)
  obtain ⟨V,CW,hVc,hVs,hVone,hCW,hVderiv,hwindow⟩ :=
    FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  let P := momentConstant K Lwin CW CF
  let B : ℝ := 2^J*(FourierBridge.coefficientMomentBound 0 P + FourierBridge.coefficientMomentBound J P)
  have hP : 0 ≤ P := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity) (add_nonneg
      (FourierBridge.coefficientMomentBound_nonneg 0 P hP)
      (FourierBridge.coefficientMomentBound_nonneg J P hP))
  refine ⟨B/m^A,by positivity,?_⟩
  intro F hF hEuler R hR
  let b : SchwartzMap ℝ ℂ := 𝓕 (positiveLogProfile V F R hVc hVs hF hR)
  refine ⟨b,?_,?_⟩
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 → V (∑ j : ι, a j*y j)=1 :=
      FourierBridge.coupled_cutoff_active W V a y M hWwindow (by simpa [T] using hVone)
    simpa [b] using coupled_positive_log_separation W F V R a y hVc hVs hF hR hactive
  · have hwindow' : ∀ s, (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1,(hwindow s hs).2.2⟩
    have hb := positive_log_fourier_bound V F R m Lwin CW CF A J hVc hVs hF hR
      hm hm1 hL hCW hCF (by simpa [K] using hVderiv) (by simpa only [K] using hwindow')
      (by simpa [K] using hEuler)
    simpa [B,P,b,K,Lwin,m] using hb

/-- The separated coefficients are Schwartz functions, so every polynomial
height moment used in (5.6) and the spectral test is genuinely integrable. -/
theorem shifted_log_coefficient_moment_integrable (b : SchwartzMap ℝ ℂ) (J : ℕ) :
    Integrable (fun t : ℝ ↦ (1+‖t‖)^J*‖b t‖) := by
  have h0 : Integrable (fun t : ℝ ↦ ‖b t‖) := b.integrable.norm
  have hJ := b.integrable_pow_mul volume J
  have hmajor := (h0.add hJ).const_mul ((2 : ℝ)^J)
  apply hmajor.mono' (by fun_prop)
  filter_upwards [] with t
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hp := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg t) J
  have ht : (2 : ℝ)^(J-1) ≤ 2^J := pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)
  calc
    _ ≤ 2^(J-1)*(1^J+‖t‖^J)*‖b t‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ ≤ 2^J*(1^J+‖t‖^J)*‖b t‖ := by gcongr
    _ = _ := by simp only [one_pow,Pi.add_apply]; ring

end ArtinMatthews
