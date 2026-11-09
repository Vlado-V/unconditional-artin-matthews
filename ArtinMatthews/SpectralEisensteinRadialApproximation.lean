module

public import ArtinMatthews.SpectralEisensteinVerticalCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! Actual smooth compact radial approximants of h^s(1-chi(h)). The small
height cutoff is proved to disappear at each positive height. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace ArtinMatthews

def eisensteinRemainderProfile (s : ℂ) (h : ℝ) : ℂ :=
  (1-eisensteinHeightCutoff h:ℝ)*(h:ℂ)^s

def eisensteinRadialApprox (s : ℂ) (A h : ℝ) : ℂ :=
  ((1-eisensteinHeightCutoff h)*eisensteinHeightCutoff (A*h):ℝ)*(h:ℂ)^s

theorem eisensteinRadialApprox_small_zero (s : ℂ) {A h : ℝ} (hA : 0 < A)
    (hh : h ≤ 1/A) : eisensteinRadialApprox s A h=0 := by
  have hcut : A*h ≤ 1 := by
    have he := (le_div_iff₀ hA).mp hh
    nlinarith
  rw [eisensteinRadialApprox,eisensteinHeightCutoff_zero hcut]
  simp

theorem eisensteinRadialApprox_large_zero (s : ℂ) (A : ℝ) {h : ℝ} (hh : 2 ≤ h) :
    eisensteinRadialApprox s A h=0 := by
  rw [eisensteinRadialApprox,eisensteinHeightCutoff_one hh]
  simp

theorem eisensteinRadialApprox_eventually_profile (s : ℂ) {A h : ℝ}
    (hh : 2 < A*h) : eisensteinRadialApprox s A =ᶠ[𝓝 h] eisensteinRemainderProfile s := by
  have hcont : Continuous (fun t : ℝ => A*t) := continuous_const.mul continuous_id
  have hnear : ∀ᶠ t in 𝓝 h, 2 < A*t := (hcont.continuousAt.eventually (Ioi_mem_nhds hh))
  filter_upwards [hnear] with t ht
  rw [eisensteinRadialApprox,eisensteinHeightCutoff_one ht.le,eisensteinRemainderProfile,mul_one]

theorem eisensteinRadialApprox_smooth (s : ℂ) {A : ℝ} (hA : 0 < A) :
    ContDiff ℝ ∞ (eisensteinRadialApprox s A) := by
  rw [contDiff_iff_contDiffAt]
  intro h
  by_cases hh : 0 < h
  · have hp : ContDiffAt ℝ ∞ (fun t : ℝ => (t:ℂ)^s) h := by
      have hlog : ContDiffAt ℝ ∞ (fun t : ℝ => (Real.log t:ℂ)) h :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp h (Real.contDiffAt_log.mpr hh.ne')
      have he : (fun t : ℝ => (t:ℂ)^s)=ᶠ[𝓝 h]
          (fun t : ℝ => Complex.exp (s*(Real.log t:ℂ))) := by
        filter_upwards [eventually_gt_nhds hh] with t ht
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
          ← Complex.ofReal_log ht.le,mul_comm]
      exact ((contDiffAt_const.mul hlog).cexp).congr_of_eventuallyEq he
    have hc : ContDiff ℝ ∞ (fun t : ℝ =>
        ((1-eisensteinHeightCutoff t)*eisensteinHeightCutoff (A*t):ℝ)) :=
      (contDiff_const.sub eisensteinHeightCutoff_contDiff).mul
        (eisensteinHeightCutoff_contDiff.comp (contDiff_const.mul contDiff_id))
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp h hc.contDiffAt).mul hp
  · have hsmall : h < 1/A := lt_of_le_of_lt (not_lt.mp hh) (one_div_pos.mpr hA)
    have he : eisensteinRadialApprox s A =ᶠ[𝓝 h] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds hsmall] with t ht
      exact eisensteinRadialApprox_small_zero s hA ht.le
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem eisensteinRadialApprox_support (s : ℂ) {A : ℝ} (hA : 0 < A) :
    tsupport (eisensteinRadialApprox s A) ⊆ Icc (1/A) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro h hh
  by_contra hn
  have ho : h < 1/A ∨ 2 < h := by simpa only [mem_Icc,not_and_or,not_le] using hn
  rcases ho with ho | ho
  · exact hh (eisensteinRadialApprox_small_zero s hA ho.le)
  · exact hh (eisensteinRadialApprox_large_zero s A ho.le)

theorem eisensteinRadialApprox_compact (s : ℂ) {A : ℝ} (hA : 0 < A) :
    HasCompactSupport (eisensteinRadialApprox s A) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (eisensteinRadialApprox_support s hA)

theorem eisensteinRadialApprox_positive_support (s : ℂ) {A : ℝ} (hA : 0 < A) :
    tsupport (eisensteinRadialApprox s A) ⊆ Ioi (0:ℝ) :=
  fun _ h => lt_of_lt_of_le (one_div_pos.mpr hA) (eisensteinRadialApprox_support s hA h).1

theorem eisensteinRadialApprox_norm_le (s : ℂ) (A h : ℝ) (hh : 0 < h) :
    ‖eisensteinRadialApprox s A h‖ ≤ h^s.re := by
  rw [eisensteinRadialApprox,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sub_nonneg.mpr (eisensteinHeightCutoff_range h).2)
      (eisensteinHeightCutoff_range (A*h)).1),Complex.norm_cpow_eq_rpow_re_of_pos hh]
  apply mul_le_of_le_one_left (Real.rpow_nonneg hh.le _)
  calc
    (1-eisensteinHeightCutoff h)*eisensteinHeightCutoff (A*h)
        ≤ (1-eisensteinHeightCutoff h)*1 :=
      mul_le_mul_of_nonneg_left (eisensteinHeightCutoff_range (A*h)).2
        (sub_nonneg.mpr (eisensteinHeightCutoff_range h).2)
    _ ≤ 1 := by linarith [(eisensteinHeightCutoff_range h).1]

theorem eisensteinRadialApprox_tendsto (s : ℂ) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun n : ℕ => eisensteinRadialApprox s (n+1:ℕ) h) atTop
      (𝓝 (eisensteinRemainderProfile s h)) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (2/h)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  have hnh : 2 < (n+1:ℕ)*h := by
    have hnR : (k:ℝ) ≤ n := by exact_mod_cast hn
    have he := (div_lt_iff₀ hh).mp hk
    push_cast
    nlinarith
  exact ((eisensteinRadialApprox_eventually_profile s hnh).eq_of_nhds).symm

end ArtinMatthews
