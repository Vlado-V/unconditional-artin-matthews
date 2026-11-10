module

public import ArtinMatthews.SourceSturmCore
public import ArtinMatthews.SourceSturmCompactIBP
public import Mathlib.MeasureTheory.Covering.Besicovitch


set_option backward.privateInPublic true
@[expose] public section

/-! Repeated compact transfer and the exact spectral power bound. -/
namespace ArtinMatthews.SourceSturm
open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section

theorem sturmPair_eigen_step {f J : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (hJ : ContDiffOn ℝ 2 J (Ioi (0 : ℝ))) (a : ℂ)
    (he : ∀ x : ℝ, 0 < x → sturmD J x = a*J x) :
    a*sturmPair f J = sturmPair (sturmD f) J := by
  calc
    _ = sturmPair f (sturmD J) := by
      unfold sturmPair
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [he x hx]
      ring
    _ = _ := sturmPair_ibp hf hc hs hJ

theorem sturmPair_iterate_eigen (n : ℕ) {f J : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (hJ : ContDiffOn ℝ 2 J (Ioi (0 : ℝ))) (a : ℂ)
    (he : ∀ x : ℝ, 0 < x → sturmD J x = a*J x) :
    a^n * sturmPair f J = sturmPair ((sturmD^[n]) f) J := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_assoc,ih,Function.iterate_succ_apply']
    exact sturmPair_eigen_step (sturmD_iterate_smooth n hf) (sturmD_iterate_hasCompactSupport n hc)
      ((sturmD_iterate_tsupport n f).trans hs) hJ a he

theorem sturmPair_iterate_norm_bound (n : ℕ) {f J : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (hJ : ContDiffOn ℝ 2 J (Ioi (0 : ℝ))) (a : ℂ)
    (he : ∀ x : ℝ, 0 < x → sturmD J x = a*J x)
    (B : ℝ) (hB : ∀ x ∈ tsupport f, ‖J x‖ ≤ B) :
    ‖a‖^n * ‖sturmPair f J‖ ≤ B * sturmL1 ((sturmD^[n]) f) := by
  have h := congrArg norm (sturmPair_iterate_eigen n hf hc hs hJ a he)
  rw [norm_mul,norm_pow] at h
  rw [h]
  exact sturmPair_norm_le (sturmD_iterate_smooth n hf).continuous
    (sturmD_iterate_hasCompactSupport n hc) ((sturmD_iterate_tsupport n f).trans hs)
    B (fun x hx => hB x (sturmD_iterate_tsupport n f hx))

theorem sturmPair_spectral_power_bound (n : ℕ) {f J : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (hJ : ContDiffOn ℝ 2 J (Ioi (0 : ℝ))) (z : ℂ)
    (he : ∀ x : ℝ, 0 < x → sturmD J x = (-4:ℂ)*z^2*J x)
    (B : ℝ) (hB : ∀ x ∈ tsupport f, ‖J x‖ ≤ B) :
    (4*‖z‖^2)^n * ‖sturmPair f J‖ ≤ B * sturmL1 ((sturmD^[n]) f) := by
  have hn : ‖(-4:ℂ)*z^2‖ = 4*‖z‖^2 := by
    rw [norm_mul,norm_pow]
    norm_num
  rw [← hn]
  exact sturmPair_iterate_norm_bound n hf hc hs hJ ((-4:ℂ)*z^2) he B hB

theorem sturmPair_spectral_div_bound (n : ℕ) {f J : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (hJ : ContDiffOn ℝ 2 J (Ioi (0 : ℝ))) (z : ℂ) (hz : z ≠ 0)
    (he : ∀ x : ℝ, 0 < x → sturmD J x = (-4:ℂ)*z^2*J x)
    (B : ℝ) (hB : ∀ x ∈ tsupport f, ‖J x‖ ≤ B) :
    ‖sturmPair f J‖ ≤ (B * sturmL1 ((sturmD^[n]) f)) / (4*‖z‖^2)^n := by
  have hp : 0 < (4*‖z‖^2)^n := pow_pos (mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr hz) _)) _
  apply (le_div_iff₀ hp).mpr
  rw [mul_comm]
  exact sturmPair_spectral_power_bound n hf hc hs hJ z he B hB

end
end ArtinMatthews.SourceSturm
