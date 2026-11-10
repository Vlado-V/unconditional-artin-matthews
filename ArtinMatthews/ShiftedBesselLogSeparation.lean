module

public import ArtinMatthews.ShiftedVoronoiBesselTransform
public import OAI.NumberTheory.DirichletL.Mellin.LogProfiles
public import ArtinMatthews.ShiftedBesselScale
public import ArtinMatthews.ShiftedLogSeparationUniform
public import ArtinMatthews.ShiftedVoronoiBesselDecay
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import OAI.NumberTheory.DirichletL.Poisson.RadialFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Actual log separation of the weight-one Bessel kernel, with constants
uniform over source families controlled by finite Schwartz seminorms. -/

noncomputable section
open Complex MeasureTheory Set OAI
open OAI.EisensteinSchwartzPoisson OAI.LocalLogFourier
open scoped ContDiff

namespace ArtinMatthews

/-- Positive-axis smoothness follows from the already identified Schwartz
radial Fourier transform. -/
theorem weightOneBesselTransform_contDiffOn (W : SchwartzMap ℝ ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hW : Function.support W ⊆ Icc 0 B) :
    ContDiffOn ℝ ∞ (weightOneBesselTransform W) (Ioi 0) := by
  have hc : ContDiffOn ℝ ∞
      (fun y : ℝ ↦ ((Real.sqrt 3 : ℂ)*Complex.I)*paperRadialFourier W (3*y)) (Ioi 0) :=
    contDiffOn_const.mul ((paperRadialFourier_contDiffOn W).comp (by fun_prop)
      (fun y hy ↦ show 3*y ∈ Ioi 0 from mul_pos (by norm_num : (0 : ℝ) < 3) hy))
  apply hc.congr
  intro y hy
  exact weightOneBesselTransform_eq_radialFourier W B hB hW y hy

/-- Genuine scaled Bessel log separation, with a uniform constant chosen
before the source W and scale K. The finite source-seminorm hypothesis is
subsequently discharged for the actual shifted source cutoffs. -/
theorem scaled_bessel_log_separation_source_bounds
    {ι : Type*} [Fintype ι]
    (V : ι → ℝ → ℂ) (a M : ι → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hVwindow : ∀ j z, V j z ≠ 0 → |z| ≤ M j) (A J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∀ C0 : ℝ, 0 ≤ C0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (B : ℝ), 0 ≤ B → Function.support W ⊆ Icc 0 B →
        s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ C0 →
        ∀ (K R : ℝ), 0 < K → 0 < R → ∃ b : SchwartzMap ℝ ℂ,
          (∀ y : ι → ℝ, (∏ j : ι, V j (y j)) *
            weightOneBesselTransform (fun x ↦ W (x/K)) (R*Real.exp (∑ j : ι, a j*y j)) =
              ∫ t : ℝ, (∏ j : ι, V j (y j)*FourierBridge.logPhase t (a j*y j))*b t) ∧
          (1+K*R)^A * (∫ t : ℝ, (1+‖t‖)^J*‖b t‖) ≤ C*K := by
  obtain ⟨s,CB,hCB,hEuler⟩ :=
    weightOneBesselTransform_euler_source_bound A (J+(volume : Measure ℝ).integrablePower)
  refine ⟨s,?_⟩
  intro C0 hC0
  obtain ⟨C,hC,hsep⟩ := coupled_log_separation_uniform_family V a M hM hVwindow A J
    (CB*C0) (mul_nonneg hCB.le hC0)
  refine ⟨C,hC,?_⟩
  intro W B hB hW hs K R hK hR
  have he : ∀ i ≤ J+(volume : Measure ℝ).integrablePower, ∀ x : ℝ, 0 < x →
      (1+x)^A*‖eulerDeriv (weightOneBesselTransform W) i x‖ ≤ CB*C0 := by
    intro i hi x hx
    exact (hEuler W B hB hW i hi x hx).trans (mul_le_mul_of_nonneg_left hs hCB.le)
  obtain ⟨b,hb,hbound⟩ := hsep (weightOneBesselTransform W)
    (weightOneBesselTransform_contDiffOn W B hB hW) he (K*R) (mul_pos hK hR)
  have hscale (t : ℝ) : ((K : ℂ) • b) t = (K : ℂ)*b t := rfl
  refine ⟨(K : ℂ) • b,?_,?_⟩
  · intro y
    rw [weightOneBesselTransform_dilate W K _ hK]
    have harg : K*(R*Real.exp (∑ j : ι, a j*y j)) = (K*R)*Real.exp (∑ j : ι, a j*y j) := by ring
    rw [harg]
    calc
      _ = (K : ℂ)*((∏ j : ι, V j (y j))*
          weightOneBesselTransform W ((K*R)*Real.exp (∑ j : ι, a j*y j))) := by ring
      _ = (K : ℂ)*(∫ t : ℝ, (∏ j : ι, V j (y j)*FourierBridge.logPhase t (a j*y j))*b t) := by rw [hb y]
      _ = _ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        rw [hscale]
        ring
  · have hi : (∫ t : ℝ, (1+‖t‖)^J*‖(K : ℂ)*b t‖) =
        K*(∫ t : ℝ, (1+‖t‖)^J*‖b t‖) := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hK]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring
    simp only [hscale]
    rw [hi]
    have hh := mul_le_mul_of_nonneg_left hbound hK.le
    nlinarith

end ArtinMatthews
