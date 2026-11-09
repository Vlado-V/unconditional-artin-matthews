module

public import ArtinMatthews.SpectralABLOppositeKWeight
public import ArtinMatthews.SpectralWeylABLBound
public import ArtinMatthews.SpectralHeatKernelLimit


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Filter MeasureTheory Complex
open scoped Topology ContDiff
noncomputable section

theorem spectralABLCoshCancellation_ne_zero_of_strip {z : ℂ} (hz : |z.im| < 3/2) :
    spectralABLCoshCancellation z ≠ 0 := by
  unfold spectralABLCoshCancellation
  have hp : 0 < ((3/2 : ℂ)+I*z).re := by
    norm_num [Complex.mul_re]
    linarith [(abs_lt.mp hz).2]
  have hm : 0 < ((3/2 : ℂ)-I*z).re := by
    norm_num [Complex.mul_re]
    linarith [(abs_lt.mp hz).1]
  exact div_ne_zero (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hp)
    (Complex.Gamma_ne_zero_of_re_pos hm)) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

theorem spectralABLCoshCancellation_inv_strip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t y : ℝ, |y| ≤ 5/8 →
      ‖(spectralABLCoshCancellation ((t : ℂ)+(y : ℂ)*I))⁻¹‖ ≤
        C*(1+t^2)*Real.exp (Real.pi*|t|) := by
  obtain ⟨D,hD,hΓ⟩ := spectral_inv_gamma_closed_strip_bound 2 (by norm_num)
  refine ⟨2*Real.pi*D^2,by positivity,?_⟩
  intro t y hy
  let z : ℂ := (t : ℂ)+(y : ℂ)*I
  have hp := hΓ (1-y) t (by linarith [(abs_le.mp hy).2]) (by linarith [(abs_le.mp hy).1])
  have hm := hΓ (1+y) (-t) (by linarith [(abs_le.mp hy).1]) (by linarith [(abs_le.mp hy).2])
  have hep : (((1-y+1/2 : ℝ) : ℂ)+(t : ℂ)*I) = 3/2+I*z := by
    dsimp [z]; push_cast; ring_nf; simp only [I_sq]; ring
  have hem : (((1+y+1/2 : ℝ) : ℂ)+((-t : ℝ) : ℂ)*I) = 3/2-I*z := by
    dsimp [z]; push_cast; ring_nf; simp only [I_sq]; ring
  rw [hep] at hp
  rw [hem,abs_neg] at hm
  have hs : (1+|t|)^2 ≤ 2*(1+t^2) := by
    nlinarith [sq_abs t,sq_nonneg (|t|-1)]
  change ‖(spectralABLCoshCancellation z)⁻¹‖ ≤ _
  rw [spectralABLCoshCancellation,inv_div,div_eq_mul_inv,mul_inv_rev,norm_mul,norm_mul,
    Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ ≤ Real.pi*(D*(1+|t|)*Real.exp (Real.pi*|t|/2))^2 := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hm hp (norm_nonneg _) (by positivity)) Real.pi_pos.le
    _ = Real.pi*D^2*((1+|t|)^2*Real.exp (Real.pi*|t|)) := by
      rw [mul_pow,mul_pow,pow_two (Real.exp _),← Real.exp_add,
        show Real.pi*|t|/2+Real.pi*|t|/2 = Real.pi*|t| by ring]
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hs (Real.exp_nonneg (Real.pi*|t|)))
        (show 0 ≤ Real.pi*D^2 by positivity)
      convert h using 1 <;> ring

/-- Any actual exponentially normalized test can use the previously
verified J and K Gaussian contour estimates. -/
theorem spectralWeylHeat_small_of_exp_rapid (H : ℂ → ℂ)
    (heven : ∀ z : ℂ, H (-z) = H z)
    (hhol : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 5/8 → DifferentiableAt ℂ H z)
    (D : ℝ) (hD : 0 ≤ D)
    (hdecay : ∀ t y : ℝ, 0 ≤ y → y ≤ 5/8 →
      (1+t^2)^3*Real.exp (Real.pi*|t|)*‖H ((t : ℂ)+(y : ℂ)*I)‖ ≤ D)
    (m n : ℤ) (X₀ : ℝ) (hX₀ : 0 < X₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ X : ℝ, 0 < X → X ≤ X₀ →
      ‖spectralABLHeatKernel H R m n X‖ ≤ C*X^(1/4 : ℝ) := by
  let base : ℂ → ℂ := fun z => H z/spectralABLCoshCancellation z
  let W : ℂ → ℂ := fun z => base z*spectralABLCoshCancellation z
  have heq {z : ℂ} (hz : |z.im| < 3/2) : W z = H z :=
    div_mul_cancel₀ _ (spectralABLCoshCancellation_ne_zero_of_strip hz)
  have haxis (t : ℝ) : W (t : ℂ) = H (t : ℂ) := heq (by norm_num)
  have hEven (z : ℂ) : W (-z) = W z := by
    simp only [W,base,heven,spectralABLCoshCancellation_even]
  have hW (z : ℂ) (hz0 : 0 ≤ z.im) (hz1 : z.im ≤ 5/8) : DifferentiableAt ℂ W z := by
    have hOpen : IsOpen {w : ℂ | |w.im| < (3/2 : ℝ)} :=
      isOpen_lt Complex.continuous_im.abs continuous_const
    have hmem : z ∈ {w : ℂ | |w.im| < (3/2 : ℝ)} := by
      change |z.im| < 3/2
      rw [abs_of_nonneg hz0]
      linarith
    apply (hhol z hz0 hz1).congr_of_eventuallyEq
    filter_upwards [hOpen.mem_nhds hmem] with w hw
    exact heq hw
  obtain ⟨G,hG,hg⟩ := spectralABLCoshCancellation_inv_strip_bound
  have hb (t y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 5/8) :
      ‖base ((t : ℂ)+(y : ℂ)*I)‖ ≤ (G*(D+1))/(1+t^2)^2 := by
    let z : ℂ := (t : ℂ)+(y : ℂ)*I
    let u : ℝ := 1+t^2
    let E := Real.exp (Real.pi*|t|)
    have hu : 0 < u := by dsimp [u]; positivity
    have hs : E*‖H z‖ ≤ D/u^3 := (le_div_iff₀ (pow_pos hu _)).mpr
      (by simpa only [z,E,u,mul_assoc,mul_comm,mul_left_comm] using hdecay t y hy0 hy1)
    have hG' : ‖(spectralABLCoshCancellation z)⁻¹‖ ≤ G*u*E :=
      hg t y (by simpa only [abs_of_nonneg hy0] using hy1)
    change ‖H z/spectralABLCoshCancellation z‖ ≤ _
    rw [div_eq_mul_inv,norm_mul]
    calc
      _ ≤ ‖H z‖*(G*u*E) := mul_le_mul_of_nonneg_left hG' (norm_nonneg _)
      _ = (E*‖H z‖)*(G*u) := by ring
      _ ≤ (D/u^3)*(G*u) := mul_le_mul_of_nonneg_right hs (by positivity)
      _ = G*D/u^2 := by field_simp [hu.ne'] <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right (by gcongr; linarith) (by positivity)
  have hB : 0 < G*(D+1) := by positivity
  have hw (R X : ℝ) : spectralABLHeatKernel H R m n X = spectralABLHeatKernel W R m n X := by
    unfold spectralABLHeatKernel
    simp_rw [haxis]
  by_cases hmn : 0 < m*n
  · obtain ⟨C,hC,hb'⟩ := spectralWeylJGaussian_small_of_base W base hEven (fun _ => rfl) hW hB hb hX₀
    refine ⟨C,hC.le,fun R hR X hX hXX => ?_⟩
    rw [hw]
    simpa only [spectralABLHeatKernel,spectralWeylIntegerSignMultiplier,ite_eq_left hmn] using
      hb' R X hR hX hXX
  · obtain ⟨C,hC,hb'⟩ := spectralWeylKGaussian_small_of_base W base hEven (fun _ => rfl) hW hB hb hX₀
    refine ⟨C,hC.le,fun R hR X hX hXX => ?_⟩
    rw [hw]
    simpa only [spectralABLHeatKernel,spectralWeylIntegerSignMultiplier,ite_eq_right hmn] using
      hb' R X hR hX hXX

end
end ArtinMatthews

