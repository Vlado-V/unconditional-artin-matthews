module

public import ArtinMatthews.SourceSturmCore
public import ArtinMatthews.SpectralJForwardTransform
public import ArtinMatthews.SourceSturmSpectralPowers
public import ArtinMatthews.SpectralJForwardSturm


set_option backward.privateInPublic true
@[expose] public section

/-! Repeated compact transfer turns any proved polynomial kernel bound
on the original support into arbitrary spectral power decay. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace ArtinMatthews
open SourceSturm

theorem spectralJForwardTransform_tail_of_kernel {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (k d : ℕ) {z : ℂ} (hz : 1 ≤ |z.re|) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ x ∈ tsupport f, ‖spectralJForwardKernel z x‖ ≤ C*(1+|z.re|)^d) :
    ‖spectralJForwardTransform f z‖ ≤
      (C*sturmL1 ((sturmD^[k+d]) f))/(1+|z.re|)^k := by
  let T := 1+|z.re|
  let L := sturmL1 ((sturmD^[k+d]) f)
  have hL : 0 ≤ L := by
    unfold L sturmL1
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact div_nonneg (norm_nonneg _) (show 0 ≤ x from (show 0 < x from hx).le)
  have hT : 0 < T := by dsimp [T]; linarith
  have hn : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have h₁ : 1 ≤ ‖z‖ := hz.trans hn
  have hz₀ : z ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le h₁)
  have hTle : T ≤ 4*‖z‖^2 := by
    dsimp only [T]
    nlinarith only [h₁,hn,mul_nonneg (sub_nonneg.mpr h₁) (norm_nonneg z)]
  have hPow := pow_le_pow_left₀ hT.le hTle (k+d)
  have hb := sturmPair_spectral_div_bound (k+d) hf hc hp
    (spectralJForwardKernel_spatial_contDiffOn hz₀) z hz₀
    (spectralJForwardKernel_sturm_eigen hz₀) (C*T^d) hB
  calc
    _ ≤ (C*T^d*L)/(4*‖z‖^2)^(k+d) := hb
    _ ≤ (C*T^d*L)/T^(k+d) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hT _) hPow
    _ = _ := by
      change (C*T^d*L)/T^(k+d) = (C*L)/T^k
      rw [pow_add]
      field_simp [hT.ne'] <;> ring

end ArtinMatthews
