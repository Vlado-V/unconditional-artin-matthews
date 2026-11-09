module

public import ArtinMatthews.SpectralABLOppositeKTransform
public import ArtinMatthews.SpectralKLCompactWideRapid
public import ArtinMatthews.SpectralABLOrderMultiplier
public import ArtinMatthews.SpectralKOrderDominance


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex OAI.CubicEisenstein
open scoped ContDiff ComplexConjugate
noncomputable section

theorem spectralABLOppositeFourierWeight_entire (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    Differentiable ℂ (spectralABLOppositeFourierWeight f) := by
  unfold spectralABLOppositeFourierWeight
  exact ((spectralKLCompactOrderTransform_entire f hf hc hp).comp
    (differentiable_id.const_mul (2*I))).const_mul _

theorem spectralABLOppositeFourierWeight_even (f : ℝ → ℂ)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (z : ℂ) :
    spectralABLOppositeFourierWeight f (-z) = spectralABLOppositeFourierWeight f z := by
  rw [spectralABLOppositeFourierWeight,spectralABLOppositeFourierWeight,mul_neg,
    spectralKLCompactOrderTransform_even f hp]

theorem spectralABLOppositeFourierWeight_real_smooth (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ContDiff ℝ ∞ (fun t : ℝ => spectralABLOppositeFourierWeight f (t : ℂ)) :=
  (spectralABLOppositeFourierWeight_entire f hf hc hp).contDiff.restrict_scalars ℝ |>.comp
    Complex.ofRealCLM.contDiff

theorem spectralABLOppositeFourierWeight_normalized_rapid (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, |y| ≤ 3/4 →
      (1+t^2)^N * Real.exp (Real.pi*|t|) *
        ‖spectralABLOppositeFourierWeight f ((t : ℂ)+(y : ℂ)*I)‖ ≤ C := by
  obtain ⟨D,hD,hb⟩ := spectralKLCompactOrderTransform_wide_rapid f hf hc hp N
  refine ⟨(2/Real.pi)*D,by positivity,?_⟩
  intro t y hy
  have hy' : |-(2*y)| ≤ (3/2 : ℝ) := by
    rw [abs_neg,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have h := hb (-(2*y)) (2*t) hy'
  have harg : ((-(2*y) : ℝ) : ℂ)+((2*t : ℝ) : ℂ)*I =
      2*I*((t : ℂ)+(y : ℂ)*I) := by
    push_cast
    ring_nf
    simp only [I_sq]
    ring
  rw [harg,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    show Real.pi*(2*|t|)/2 = Real.pi*|t| by ring] at h
  have hp' : (1+t^2)^N ≤ (1+(2*t)^2)^N :=
    pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg t]) _
  rw [spectralABLOppositeFourierWeight,norm_mul,norm_div,
    show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num,Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ = (2/Real.pi)*((1+t^2)^N*Real.exp (Real.pi*|t|)*
        ‖spectralKLCompactOrderTransform f (2*I*((t : ℂ)+(y : ℂ)*I))‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp' (Real.exp_nonneg _))
        (norm_nonneg _)).trans h) (by positivity)

theorem spectralABLOppositeFourierWeight_strip_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, |y| ≤ 3/4 →
      ‖spectralABLOppositeFourierWeight f ((t : ℂ)+(y : ℂ)*I)‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := spectralABLOppositeFourierWeight_normalized_rapid f hf hc hp 0
  refine ⟨C,hC,?_⟩
  intro t y hy
  have hE : 1 ≤ Real.exp (Real.pi*|t|) := Real.one_le_exp (by positivity)
  simpa only [pow_zero,one_mul] using
    (mul_le_mul_of_nonneg_right hE (norm_nonneg
      (spectralABLOppositeFourierWeight f ((t : ℂ)+(y : ℂ)*I)))).trans
      (by simpa only [pow_zero,one_mul] using hb t y hy)

theorem spectralKLCompactOrderTransform_star_of_axis (f : ℝ → ℂ)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (hf : ∀ x, star (f x) = f x)
    (ν : ℂ) (hν : ν.im = 0 ∨ ν.re = 0) :
    star (spectralKLCompactOrderTransform f ν) = spectralKLCompactOrderTransform f ν := by
  have hK (x : ℝ) (hx : 0 < x) : conj (schlafliBesselK ν x) = schlafliBesselK ν x := by
    rcases hν with h | h
    · have he : ν = (ν.re : ℂ) := by apply Complex.ext <;> simp [h]
      rw [he,schlafliBesselK_real_nonneg _ hx,conj_ofReal]
    · have he : ν = (ν.im : ℂ)*I := by apply Complex.ext <;> simp [h,Complex.mul_re,Complex.mul_im]
      rw [he,schlafliBesselK_imaginary_eq_realKernel _ hx,conj_ofReal]
  change conj _ = _
  rw [spectralKLCompactOrderTransform_integral f hp,← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change conj (schlafliBesselK ν x*f x/(x : ℂ)) = _
  have hf' : conj (f x) = f x := hf x
  simp only [map_div₀,map_mul,conj_ofReal,hK x hx,hf']

theorem spectralABLOppositeFourierWeight_star_of_axis (f : ℝ → ℂ)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (hf : ∀ x, star (f x) = f x)
    (z : ℂ) (hz : z.im = 0 ∨ z.re = 0) :
    star (spectralABLOppositeFourierWeight f z) = spectralABLOppositeFourierWeight f z := by
  have ho : (2*I*z).im = 0 ∨ (2*I*z).re = 0 := by
    rcases hz with h | h
    · right; norm_num [Complex.mul_re,Complex.mul_im,h]
    · left; norm_num [Complex.mul_re,Complex.mul_im,h]
  have h := spectralKLCompactOrderTransform_star_of_axis f hp hf (2*I*z) ho
  unfold spectralABLOppositeFourierWeight
  change conj _ = _
  have h' : conj (spectralKLCompactOrderTransform f (2*I*z)) =
      spectralKLCompactOrderTransform f (2*I*z) := h
  simp only [map_mul,map_div₀,map_ofNat,conj_ofReal,h']

def spectralABLOppositeEnergyTest (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) : SpectralEnergyTest :=
  spectralSourceEnergyTest (spectralABLOppositeFourierWeight f)
    (fun z _ => (spectralABLOppositeFourierWeight_entire f hf.continuous hc hp z).continuousAt)
    (Classical.choose (spectralABLOppositeFourierWeight_strip_bound f hf hc hp))
    (fun t => by
      have h := (Classical.choose_spec (spectralABLOppositeFourierWeight_strip_bound f hf hc hp)).2
        t 0 (by norm_num)
      simpa only [Complex.ofReal_zero,zero_mul,add_zero] using h)

theorem spectralABLOppositeEnergyTest_apply (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (l : Ici (0 : ℝ)) :
    spectralABLOppositeEnergyTest f hf hc hp l =
      spectralABLOppositeFourierWeight f (spectralSourceParameter l) := rfl

theorem spectralABLOppositeEnergyTest_order (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (l : Ici (0 : ℝ)) :
    spectralABLOppositeEnergyTest f hf hc hp l =
      spectralABLOppositeFourierWeight f (-I*Complex.sqrt (1/4-((l : ℝ) : ℂ))) := by
  rw [spectralABLOppositeEnergyTest_apply]
  exact spectralEven_eq_of_square_eq _ (spectralABLOppositeFourierWeight_even f hp) _ _
    (spectralSourceParameter_order_square l)

theorem spectralABLOppositeEnergyTest_continuous_symbol (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (t : ℝ) :
    spectralContinuousTestSymbol (spectralABLOppositeEnergyTest f hf hc hp) t =
      spectralABLOppositeFourierWeight f (t : ℂ) :=
  spectralSourceEnergyTest_continuous_symbol _ _ _ _ (spectralABLOppositeFourierWeight_even f hp) t

theorem spectralABLOppositeEnergyTest_real (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hreal : ∀ x, star (f x) = f x) (l : Ici (0 : ℝ)) :
    star (spectralABLOppositeEnergyTest f hf hc hp l) = spectralABLOppositeEnergyTest f hf hc hp l := by
  rw [spectralABLOppositeEnergyTest_apply]
  apply spectralABLOppositeFourierWeight_star_of_axis f hp hreal
  by_cases hl : (1/4 : ℝ) ≤ l
  · left
    simp [spectralSourceParameter_principal _ hl]
  · right
    unfold spectralSourceParameter
    rw [Real.sqrt_eq_zero_of_nonpos (by linarith : (l : ℝ)-1/4 ≤ 0)]
    simp [Complex.mul_re]

end
end ArtinMatthews

