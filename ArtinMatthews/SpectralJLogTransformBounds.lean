module

public import ArtinMatthews.SpectralJLogSeminorm
public import ArtinMatthews.SpectralJForwardKernelQuantitative
public import ArtinMatthews.SpectralJForwardSturm


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative real and complementary transform bounds for the actual
fixed-amplitude logarithmic source family. -/
namespace ArtinMatthews
open Set MeasureTheory
open SourceSturm
open scoped ContDiff
noncomputable section

private theorem spectralJLogScale_log_bound {a α β x : ℝ}
    (ha : 0 < a) (hx : x ∈ Icc (a*Real.exp α) (a*Real.exp β)) :
    |Real.log x| ≤ |Real.log a|+max |α| |β| := by
  have hx0 : 0 < x := (mul_pos ha (Real.exp_pos _)).trans_le hx.1
  have h₁ := Real.log_le_log (mul_pos ha (Real.exp_pos α)) hx.1
  have h₂ := Real.log_le_log hx0 hx.2
  rw [Real.log_mul ha.ne' (Real.exp_pos α).ne', Real.log_exp] at h₁
  rw [Real.log_mul ha.ne' (Real.exp_pos β).ne', Real.log_exp] at h₂
  have ha' := le_abs_self (Real.log a)
  have hb' := neg_abs_le (Real.log a)
  have hα : -max |α| |β| ≤ α := by
    have h := le_max_left |α| |β|
    linarith [neg_abs_le α]
  have hβ : β ≤ max |α| |β| := (le_abs_self β).trans (le_max_right _ _)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem spectralJLogScale_rpow_bound {a α β x κ : ℝ}
    (ha : 0 < a) (hx : x ∈ Icc (a*Real.exp α) (a*Real.exp β))
    (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1/4) :
    x^(-2*κ) ≤ a^(-2*κ)*Real.exp (max |α| |β|) := by
  have hp : α*(-2*κ) ≤ max |α| |β| := by
    calc
      _ ≤ |α*(-2*κ)| := le_abs_self _
      _ = |α| * (2*κ) := by
        rw [abs_mul, abs_of_nonpos (by linarith : -2*κ ≤ 0)]
        ring
      _ ≤ |α| := mul_le_of_le_one_right (abs_nonneg _) (by linarith)
      _ ≤ _ := le_max_left _ _
  calc
    _ ≤ (a*Real.exp α)^(-2*κ) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos ha (Real.exp_pos _)) hx.1 (by linarith)
    _ = a^(-2*κ)*Real.exp (α*(-2*κ)) := by
      rw [Real.mul_rpow ha.le (Real.exp_pos α).le, ← Real.exp_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hp) (Real.rpow_nonneg ha.le _)

theorem spectralJOscillatoryLogProfile_real_basic
    (A : ℝ → ℂ) (B : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    {α β : ℝ} (hs : tsupport A ⊆ Icc α β) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u t : ℝ, 0 < a → a ≤ R →
      ‖spectralJForwardTransform (spectralJOscillatoryLogProfile A B a u) (t : ℂ)‖ ≤
        C*(1+|Real.log a|) := by
  obtain ⟨K₁,hK₁,hsmall⟩ := spectralJForwardKernel_real_small_bound (R*Real.exp β)
  obtain ⟨K₂,hK₂,hlarge⟩ := spectralJForwardKernel_real_large_bound
  obtain ⟨D,hD,hL⟩ := spectralJOscillatoryLogProfile_sturmL1 A B hA hB hs R hR 0
  let L := max |α| |β|
  let K := max K₁ K₂
  have hL0 : 0 ≤ L := (abs_nonneg α).trans (le_max_left _ _)
  have hK : 0 < K := hK₁.trans_le (le_max_left _ _)
  refine ⟨K*(1+L)*D, by positivity, ?_⟩
  intro a u t ha haR
  let f := spectralJOscillatoryLogProfile A B a u
  have hgs : tsupport (markedOscillatoryFamily A B u) ⊆ Icc α β :=
    (spectralJOscillatoryFamily_tsupport A B u).trans hs
  have hfs : tsupport f ⊆ Icc (a*Real.exp α) (a*Real.exp β) :=
    spectralJLogProfile_tsupport ha hgs
  have hfp : tsupport f ⊆ Ioi 0 := spectralJLogProfile_positive_tsupport ha hgs
  have hf : ContDiff ℝ ∞ f := spectralJOscillatoryLogProfile_smooth A B hA hB hs ha u
  have hfc : HasCompactSupport f := spectralJLogProfile_hasCompactSupport ha hgs
  have hk (x : ℝ) (hx : x ∈ tsupport f) :
      ‖spectralJForwardKernel (t : ℂ) x‖ ≤ K*(1+L)*(1+|Real.log a|) := by
    have hx0 : 0 < x := hfp hx
    have hxB : x ≤ R*Real.exp β :=
      (hfs hx).2.trans (mul_le_mul_of_nonneg_right haR (Real.exp_pos _).le)
    have hlog := spectralJLogScale_log_bound ha (hfs hx)
    rcases le_or_gt |t| 1 with ht|ht
    · calc
        _ ≤ K₁*(1+|Real.log x|) := hsmall t x ht hx0 hxB
        _ ≤ K*((1+L)*(1+|Real.log a|)) := by
          apply mul_le_mul (le_max_left _ _) _ (by positivity) hK.le
          dsimp only [L] at *
          nlinarith [mul_nonneg hL0 (abs_nonneg (Real.log a))]
        _ = _ := by ring
    · calc
        _ ≤ K₂ := hlarge t x ht.le hx0
        _ ≤ K := le_max_right _ _
        _ ≤ K*(1+L) :=
          le_mul_of_one_le_right hK.le (by linarith)
        _ ≤ K*(1+L)*(1+|Real.log a|) :=
          le_mul_of_one_le_right (mul_nonneg hK.le (by linarith))
            (by linarith [abs_nonneg (Real.log a)])
  have hnorm := sturmPair_norm_le hf.continuous hfc hfp
    (K*(1+L)*(1+|Real.log a|)) hk
  have hl : sturmL1 f ≤ D := by
    simpa only [Function.iterate_zero, id_eq, Nat.mul_zero, pow_zero, mul_one] using hL a u ha haR
  change ‖sturmPair f (spectralJForwardKernel (t : ℂ))‖ ≤ _
  exact (hnorm.trans (mul_le_mul_of_nonneg_left hl (by positivity))).trans_eq (by ring)

theorem spectralJOscillatoryLogProfile_real_power
    (A : ℝ → ℂ) (B : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    {α β : ℝ} (hs : tsupport A ⊆ Icc α β) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u t : ℝ, 0 < a → a ≤ R → 1 ≤ |t| →
      (4*t^2)^n * ‖spectralJForwardTransform (spectralJOscillatoryLogProfile A B a u) (t : ℂ)‖ ≤
        C*(1+|u|)^(2*n) := by
  obtain ⟨K,hK,hkernel⟩ := spectralJForwardKernel_real_large_bound
  obtain ⟨D,hD,hL⟩ := spectralJOscillatoryLogProfile_sturmL1 A B hA hB hs R hR n
  refine ⟨K*D, mul_pos hK hD, ?_⟩
  intro a u t ha haR ht
  let f := spectralJOscillatoryLogProfile A B a u
  have hgs : tsupport (markedOscillatoryFamily A B u) ⊆ Icc α β :=
    (spectralJOscillatoryFamily_tsupport A B u).trans hs
  have hfp : tsupport f ⊆ Ioi 0 := spectralJLogProfile_positive_tsupport ha hgs
  have hf : ContDiff ℝ ∞ f := spectralJOscillatoryLogProfile_smooth A B hA hB hs ha u
  have hfc : HasCompactSupport f := spectralJLogProfile_hasCompactSupport ha hgs
  have ht0 : (t : ℂ) ≠ 0 := by
    intro he
    have hz : t = 0 := Complex.ofReal_eq_zero.mp he
    simp only [hz, abs_zero] at ht
    linarith
  have h := sturmPair_spectral_power_bound n hf hfc hfp
    (spectralJForwardKernel_spatial_contDiffOn ht0) (t : ℂ)
    (fun x hx => spectralJForwardKernel_sturm_eigen ht0 x hx) K
    (fun x hx => hkernel t x ht (hfp hx))
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  change (4*t^2)^n * ‖sturmPair f (spectralJForwardKernel (t : ℂ))‖ ≤ _
  exact (h.trans (mul_le_mul_of_nonneg_left (hL a u ha haR) hK.le)).trans_eq (by ring)

theorem spectralJOscillatoryLogProfile_exceptional
    (A : ℝ → ℂ) (B : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    {α β : ℝ} (hs : tsupport A ⊆ Icc α β) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u κ : ℝ, 0 < a → a ≤ R → 0 ≤ κ → κ ≤ 1/4 →
      ‖spectralJForwardTransform (spectralJOscillatoryLogProfile A B a u) ((κ : ℂ)*Complex.I)‖ ≤
        C*(1+|Real.log a|)*a^(-2*κ) := by
  obtain ⟨K,hK,hkernel⟩ := spectralJForwardKernel_exceptional_bound (R*Real.exp β)
  obtain ⟨D,hD,hL⟩ := spectralJOscillatoryLogProfile_sturmL1 A B hA hB hs R hR 0
  let L := max |α| |β|
  have hL0 : 0 ≤ L := (abs_nonneg α).trans (le_max_left _ _)
  refine ⟨K*Real.exp L*(1+L)*D, by positivity, ?_⟩
  intro a u κ ha haR hκ hκ₁
  let f := spectralJOscillatoryLogProfile A B a u
  have hgs : tsupport (markedOscillatoryFamily A B u) ⊆ Icc α β :=
    (spectralJOscillatoryFamily_tsupport A B u).trans hs
  have hfs : tsupport f ⊆ Icc (a*Real.exp α) (a*Real.exp β) :=
    spectralJLogProfile_tsupport ha hgs
  have hfp : tsupport f ⊆ Ioi 0 := spectralJLogProfile_positive_tsupport ha hgs
  have hf : ContDiff ℝ ∞ f := spectralJOscillatoryLogProfile_smooth A B hA hB hs ha u
  have hfc : HasCompactSupport f := spectralJLogProfile_hasCompactSupport ha hgs
  have hk (x : ℝ) (hx : x ∈ tsupport f) :
      ‖spectralJForwardKernel ((κ : ℂ)*Complex.I) x‖ ≤
        K*Real.exp L*(1+L)*(1+|Real.log a|)*a^(-2*κ) := by
    have hx0 : 0 < x := hfp hx
    have hxB : x ≤ R*Real.exp β :=
      (hfs hx).2.trans (mul_le_mul_of_nonneg_right haR (Real.exp_pos _).le)
    have hlog := spectralJLogScale_log_bound ha (hfs hx)
    have hpow := spectralJLogScale_rpow_bound ha (hfs hx) hκ hκ₁
    have hlog' : 1+|Real.log x| ≤ (1+L)*(1+|Real.log a|) := by
      dsimp only [L] at *
      nlinarith [mul_nonneg hL0 (abs_nonneg (Real.log a))]
    calc
      _ ≤ K*x^(-2*κ)*(1+|Real.log x|) := hkernel κ x hκ hκ₁ hx0 hxB
      _ ≤ K*(a^(-2*κ)*Real.exp L)*((1+L)*(1+|Real.log a|)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hK.le) hlog'
          (by positivity) (by positivity)
      _ = _ := by ring
  have hnorm := sturmPair_norm_le hf.continuous hfc hfp
    (K*Real.exp L*(1+L)*(1+|Real.log a|)*a^(-2*κ)) hk
  have hl : sturmL1 f ≤ D := by
    simpa only [Function.iterate_zero, id_eq, Nat.mul_zero, pow_zero, mul_one] using hL a u ha haR
  change ‖sturmPair f (spectralJForwardKernel ((κ : ℂ)*Complex.I))‖ ≤ _
  exact (hnorm.trans (mul_le_mul_of_nonneg_left hl (by positivity))).trans_eq (by ring)

end
end ArtinMatthews
