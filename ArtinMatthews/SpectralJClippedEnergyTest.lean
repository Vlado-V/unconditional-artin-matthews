module

public import ArtinMatthews.SpectralJForwardRealWeight
public import ArtinMatthews.SpectralABLEnergyWindows


set_option backward.privateInPublic true
@[expose] public section

/-! A bounded continuous energy test with the exact native values above the source gap. -/
namespace ArtinMatthews
open Set
open scoped ContDiff
noncomputable section

def spectralJClippedWeight (f : ℝ → ℂ) (l : ℝ) : ℂ :=
  let q := max (3 / 16 : ℝ) l
  (Real.pi : ℂ) * spectralJForwardTransform f (spectralSourceParameter q) *
    spectralABLCoshCancellation (spectralSourceParameter q) / (q : ℂ)

theorem spectralJClippedWeight_continuous (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    Continuous (spectralJClippedWeight f) := by
  let q (l : ℝ) := max (3 / 16 : ℝ) l
  have hq : Continuous q := continuous_const.max continuous_id
  have hq₀ (l : ℝ) : 0 < q l :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 16) (le_max_left _ _)
  have hparam : Continuous (fun l => spectralSourceParameter (q l)) :=
    spectralSourceParameter_continuous.comp hq
  have hb : Continuous (fun l => spectralJForwardTransform f (spectralSourceParameter (q l))) := by
    apply continuous_iff_continuousAt.mpr
    intro l
    have hs := spectralSourceParameter_im_bound (q l) (hq₀ l).le
    have ha : ContinuousAt (spectralJForwardTransform f) (spectralSourceParameter (q l)) :=
      (spectralJForwardTransform_analyticOnNhd f hf.continuous hc hp _
        (lt_of_le_of_lt hs (by norm_num))).continuousAt
    exact ha.comp (f := fun x : ℝ => spectralSourceParameter (q x)) (x := l) hparam.continuousAt
  have hw : Continuous (fun l => spectralABLCoshCancellation (spectralSourceParameter (q l))) := by
    apply continuous_iff_continuousAt.mpr
    intro l
    have hs := spectralSourceParameter_im_bound (q l) (hq₀ l).le
    have ha : ContinuousAt spectralABLCoshCancellation (spectralSourceParameter (q l)) :=
      (spectralABLCoshCancellation_differentiableAt _ (lt_of_le_of_lt hs (by norm_num))).continuousAt
    exact ha.comp (f := fun x : ℝ => spectralSourceParameter (q x)) (x := l) hparam.continuousAt
  exact ((continuous_const.mul hb).mul hw).div (Complex.continuous_ofReal.comp hq)
    (fun l => Complex.ofReal_ne_zero.mpr (hq₀ l).ne')

theorem spectralJClippedWeight_bounded (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℝ, ‖spectralJClippedWeight f l‖ ≤ C := by
  obtain ⟨B, hB, hb⟩ := spectralJForwardTransform_strip_rapid f hf hc hp 0
  obtain ⟨D, hD, hd⟩ := spectralABLCoshCancellation_strip_bound (1 / 2) (by norm_num) (by norm_num)
  refine ⟨Real.pi * B * D / (3 / 16), by positivity, ?_⟩
  intro l
  let q := max (3 / 16 : ℝ) l
  have hq : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 16) (le_max_left _ _)
  have hs := spectralSourceParameter_im_bound q hq.le
  have hbq : ‖spectralJForwardTransform f (spectralSourceParameter q)‖ ≤ B := by
    simpa only [pow_zero, div_one] using hb _ (le_trans hs (by norm_num))
  have hdq := hd (spectralSourceParameter q) hs
  change ‖(Real.pi : ℂ) * spectralJForwardTransform f (spectralSourceParameter q) *
    spectralABLCoshCancellation (spectralSourceParameter q) / (q : ℂ)‖ ≤ _
  rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_real, Real.norm_of_nonneg hq.le]
  calc
    _ ≤ (Real.pi * B * D) / q :=
      div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hbq Real.pi_pos.le) hdq
          (norm_nonneg _) (by positivity)) hq.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by norm_num) (le_max_left _ _)

def spectralJClippedEnergyTest (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) : SpectralEnergyTest :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun l => spectralJClippedWeight f (l : ℝ))
    ((spectralJClippedWeight_continuous f hf hc hp).comp continuous_subtype_val)
    (Classical.choose (spectralJClippedWeight_bounded f hf hc hp))
    (fun l => (Classical.choose_spec (spectralJClippedWeight_bounded f hf hc hp)).2 l)

theorem spectralJClippedEnergyTest_apply (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (l : Ici (0 : ℝ)) :
    spectralJClippedEnergyTest f hf hc hp l = spectralJClippedWeight f l := rfl

theorem spectralJClippedWeight_native (f : ℝ → ℂ) (l : ℝ) (hl : 3 / 16 ≤ l) :
    spectralJClippedWeight f l = spectralJForwardSpectralWeight f (spectralSourceParameter l) := by
  have hl₀ : 0 < l := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 16) hl
  have hc := spectralSourceParameter_cosh_ne_zero l hl₀
  have he : spectralABLCoshCancellation (spectralSourceParameter l) *
      Complex.cosh ((Real.pi : ℂ) * spectralSourceParameter l) = (l : ℂ) := by
    rw [spectralABLCoshCancellation_mul_cosh _ (spectralSourceParameter_im_lt_half l hl₀),
      spectralSourceParameter_sq]
    ring
  have he' := (eq_div_iff hc).mpr he
  rw [spectralJClippedWeight, max_eq_right hl, he', spectralJForwardSpectralWeight]
  have hlC : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl₀.ne'
  field_simp [hlC, hc] <;> ring

end
end ArtinMatthews
