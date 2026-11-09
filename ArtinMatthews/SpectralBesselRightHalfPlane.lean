module

public import ArtinMatthews.SpectralBesselFiniteEnergy
public import Mathlib.Analysis.RCLike.Sqrt


set_option backward.privateInPublic true
@[expose] public section

/-! The same genuine K classification for the closed right half-plane of
orders, including the complementary real spectral branch. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralKPrefactorBound (ν : ℂ) (δ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (δ / 2) ^ (-ν.re)

theorem spectralKPrefactorBound_nonneg (ν : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ spectralKPrefactorBound ν δ := by
  unfold spectralKPrefactorBound
  exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)

theorem spectralSchlafliPrefactor_rightHalfPlane_bound (ν : ℂ) (hν : 0 ≤ ν.re)
    (δ x : ℝ) (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖spectralSchlafliPrefactor ν x‖ ≤ spectralKPrefactorBound ν δ := by
  rw [spectralSchlafliPrefactor_norm ν x (hδ.trans_le hx), spectralKPrefactorBound]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (neg_nonpos.mpr hν)

theorem schlafliBesselK_rightHalfPlane_bound (ν : ℂ) (hν : 0 ≤ ν.re)
    (δ x : ℝ) (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖schlafliBesselK ν x‖ ≤
      (spectralKPrefactorBound ν δ * spectralSchlafliDecayConstant ν.re δ) *
        Real.exp (-x / 2) := by
  change ‖spectralSchlafliPrefactor ν x * schlafliIntegral ν x‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ spectralKPrefactorBound ν δ *
        (spectralSchlafliDecayConstant ν.re δ * Real.exp (-x / 2)) :=
      mul_le_mul (spectralSchlafliPrefactor_rightHalfPlane_bound ν hν δ x hδ hx)
        (schlafliIntegral_exponential_bound ν δ x hδ hx) (norm_nonneg _)
        (spectralKPrefactorBound_nonneg ν δ hδ)
    _ = _ := by ring

theorem schlafliBesselK_rightHalfPlane_deriv_bound (ν : ℂ) (hν : 0 ≤ ν.re)
    (δ x : ℝ) (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖deriv (schlafliBesselK ν) x‖ ≤
      (spectralKPrefactorBound ν δ *
        ((x / 2) * spectralSchlafliDecayConstant (ν.re - 1) δ +
          (‖ν‖ / δ) * spectralSchlafliDecayConstant ν.re δ)) * Real.exp (-x / 2) := by
  have hxp : 0 < x := hδ.trans_le hx
  have hb0 := schlafliIntegral_exponential_bound ν δ x hδ hx
  have hb1 := schlafliIntegral_exponential_bound (ν - 1) δ x hδ hx
  simp only [Complex.sub_re, Complex.one_re] at hb1
  have hd : ‖ν‖ / x ≤ ‖ν‖ / δ :=
    div_le_div_of_nonneg_left (norm_nonneg ν) hδ hx
  have h1 := mul_le_mul_of_nonneg_left hb1 (by positivity : 0 ≤ x / 2)
  have h2 := mul_le_mul hd hb0 (norm_nonneg (schlafliIntegral ν x))
    (div_nonneg (norm_nonneg ν) hδ.le)
  rw [schlafliBesselK_deriv ν x hxp, norm_mul, schlafliIntegral_deriv ν x hxp]
  calc
    _ ≤ spectralKPrefactorBound ν δ *
        ‖-((x : ℂ) / 2) * schlafliIntegral (ν - 1) x -
          ν / (x : ℂ) * schlafliIntegral ν x‖ :=
      mul_le_mul_of_nonneg_right
        (spectralSchlafliPrefactor_rightHalfPlane_bound ν hν δ x hδ hx) (norm_nonneg _)
    _ ≤ spectralKPrefactorBound ν δ *
        (‖-((x : ℂ) / 2) * schlafliIntegral (ν - 1) x‖ +
          ‖ν / (x : ℂ) * schlafliIntegral ν x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (spectralKPrefactorBound_nonneg ν δ hδ)
    _ = spectralKPrefactorBound ν δ *
        ((x / 2) * ‖schlafliIntegral (ν - 1) x‖ + (‖ν‖ / x) * ‖schlafliIntegral ν x‖) := by
      rw [norm_mul, norm_mul, norm_neg, norm_div, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hxp]
      norm_num
    _ ≤ spectralKPrefactorBound ν δ *
        ((x / 2) * (spectralSchlafliDecayConstant (ν.re - 1) δ * Real.exp (-x / 2)) +
          (‖ν‖ / δ) * (spectralSchlafliDecayConstant ν.re δ * Real.exp (-x / 2))) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) (spectralKPrefactorBound_nonneg ν δ hδ)
    _ = _ := by ring

theorem spectralKBesselWhittaker_rightHalfPlane_bound (ν : ℂ) (hν : 0 ≤ ν.re)
    (q y : ℝ) (hq : 0 < q) (hy : 1 ≤ y) :
    ‖spectralKBesselWhittaker ν q y‖ ≤
      (spectralKPrefactorBound ν q * spectralSchlafliDecayConstant ν.re q) *
        (y * Real.exp (-(q * y) / 2)) := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hb := schlafliBesselK_rightHalfPlane_bound ν hν q (q * y) hq (by nlinarith)
  have hs : Real.sqrt y ≤ y := Real.sqrt_le_self_iff.mpr (Or.inr hy)
  rw [spectralKBesselWhittaker_norm ν q y hy0]
  calc
    _ ≤ y * ‖schlafliBesselK ν (q * y)‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ ≤ y * ((spectralKPrefactorBound ν q * spectralSchlafliDecayConstant ν.re q) *
        Real.exp (-(q * y) / 2)) := mul_le_mul_of_nonneg_left hb hy0.le
    _ = _ := by ring

theorem spectralKBesselWhittaker_rightHalfPlane_weighted_deriv_bound
    (ν : ℂ) (hν : 0 ≤ ν.re) (q y : ℝ) (hq : 0 < q) (hy : 1 ≤ y) :
    y * ‖deriv (spectralKBesselWhittaker ν q) y‖ ≤
      ((spectralKPrefactorBound ν q * q ^ 2 * spectralSchlafliDecayConstant (ν.re - 1) q / 2) * y ^ 3 +
        (spectralKPrefactorBound ν q * ‖ν‖ * spectralSchlafliDecayConstant ν.re q) * y ^ 2 +
        (spectralKPrefactorBound ν q * spectralSchlafliDecayConstant ν.re q / 2) * y) *
          Real.exp (-(q * y) / 2) := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hqy : q ≤ q * y := by nlinarith
  have hK := schlafliBesselK_rightHalfPlane_bound ν hν q (q * y) hq hqy
  have hD := schlafliBesselK_rightHalfPlane_deriv_bound ν hν q (q * y) hq hqy
  have hs : Real.sqrt y ≤ y := Real.sqrt_le_self_iff.mpr (Or.inr hy)
  calc
    _ ≤ y * (Real.sqrt y * (q * ‖deriv (schlafliBesselK ν) (q * y)‖ +
        (1 / (2 * y)) * ‖schlafliBesselK ν (q * y)‖)) :=
      mul_le_mul_of_nonneg_left (spectralKBesselWhittaker_deriv_norm_le ν q y hq hy0) hy0.le
    _ ≤ y * (y * (q * ‖deriv (schlafliBesselK ν) (q * y)‖ +
        (1 / (2 * y)) * ‖schlafliBesselK ν (q * y)‖)) := by gcongr
    _ ≤ y * (y * (q * ((spectralKPrefactorBound ν q *
        (((q * y) / 2) * spectralSchlafliDecayConstant (ν.re - 1) q +
          (‖ν‖ / q) * spectralSchlafliDecayConstant ν.re q)) * Real.exp (-(q * y) / 2)) +
        (1 / (2 * y)) * ((spectralKPrefactorBound ν q *
          spectralSchlafliDecayConstant ν.re q) * Real.exp (-(q * y) / 2)))) := by gcongr
    _ = _ := by field_simp

theorem spectralKBesselWhittaker_rightHalfPlane_tendsto (ν : ℂ) (hν : 0 ≤ ν.re)
    (q : ℝ) (hq : 0 < q) :
    Tendsto (spectralKBesselWhittaker ν q) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim := (spectral_polynomial_exp_tendsto q hq 1).const_mul
    (spectralKPrefactorBound ν q * spectralSchlafliDecayConstant ν.re q)
  simp only [pow_one, mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  exact spectralKBesselWhittaker_rightHalfPlane_bound ν hν q y hq hy

theorem spectralKBesselWhittaker_rightHalfPlane_weighted_deriv_tendsto
    (ν : ℂ) (hν : 0 ≤ ν.re) (q : ℝ) (hq : 0 < q) :
    Tendsto (fun y : ℝ => y * ‖deriv (spectralKBesselWhittaker ν q) y‖) atTop (𝓝 0) := by
  have hlim := ((spectral_polynomial_exp_tendsto q hq 3).const_mul
    (spectralKPrefactorBound ν q * q ^ 2 * spectralSchlafliDecayConstant (ν.re - 1) q / 2)).add
    ((spectral_polynomial_exp_tendsto q hq 2).const_mul
      (spectralKPrefactorBound ν q * ‖ν‖ * spectralSchlafliDecayConstant ν.re q)) |>.add
    ((spectral_polynomial_exp_tendsto q hq 1).const_mul
      (spectralKPrefactorBound ν q * spectralSchlafliDecayConstant ν.re q / 2))
  simp only [mul_zero, add_zero, pow_one] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    exact mul_nonneg hy (norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have h := spectralKBesselWhittaker_rightHalfPlane_weighted_deriv_bound ν hν q y hq hy
    convert h using 1
    ring

theorem spectralNormalODE_rightHalfPlane_classification (ν : ℂ) (hν : 0 ≤ ν.re)
    (q Y : ℝ) (hq : 0 < q) (hY : 0 ≤ Y) (f : ℝ → ℂ)
    (hf : ∀ t, Y < t → HasDerivAt f (deriv f t) t)
    (hf' : ∀ t, Y < t → HasDerivAt (deriv f)
      (((q : ℂ) ^ 2 - (1 / 4 - ν ^ 2) / (t : ℂ) ^ 2) * f t) t)
    (henergy : IntegrableOn (fun t : ℝ => ‖deriv f t‖ ^ 2) (Ioi Y))
    (hmass : IntegrableOn (fun t : ℝ => ‖f t‖ ^ 2 / t ^ 2) (Ioi Y)) :
    ∃ c : ℂ, ∀ y, Y < y →
      f y = c * ((Real.sqrt y : ℂ) * schlafliBesselK ν (q * y)) := by
  let g := spectralKBesselWhittaker ν q
  have hg : ∀ t, Y < t → HasDerivAt g (deriv g t) t := by
    intro t ht
    have ht0 := hY.trans_lt ht
    have hd := spectralKBesselWhittaker_hasDerivAt ν q t hq ht0
    rw [← spectralKBesselWhittaker_deriv ν q t hq ht0] at hd
    exact hd
  have hg' : ∀ t, Y < t → HasDerivAt (deriv g)
      (((q : ℂ) ^ 2 - (1 / 4 - ν ^ 2) / (t : ℂ) ^ 2) * g t) t := by
    intro t ht
    exact spectralKBesselWhittaker_deriv_normal_hasDerivAt ν q t hq (hY.trans_lt ht)
  have hbound : ∀ᶠ t in atTop, ‖g t‖ ≤ 1 ∧ t * ‖deriv g t‖ ≤ 1 := by
    have hglim := (spectralKBesselWhittaker_rightHalfPlane_tendsto ν hν q hq).norm
    simp only [norm_zero] at hglim
    have hgdlim := spectralKBesselWhittaker_rightHalfPlane_weighted_deriv_tendsto ν hν q hq
    filter_upwards [hglim.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      hgdlim.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht hd
    exact ⟨ht.le, hd.le⟩
  have hW := spectralWronskian_zero_of_finite_energy
    (fun t => (q : ℂ) ^ 2 - (1 / 4 - ν ^ 2) / (t : ℂ) ^ 2) f g Y
    hf hf' hg hg' henergy hmass hbound
  obtain ⟨t₀, _, ht₀, hne⟩ := spectralKBesselWhittaker_exists_ne_zero_above ν
    (by linarith) q Y hq
  refine ⟨f t₀ / g t₀, ?_⟩
  intro y hy
  have he := spectralNormalODE_eq_mul_of_wronskian_zero (1 / 4 - ν ^ 2) q Y t₀
    hY ht₀ f g hf hf' hg hg' hne (hW t₀ ht₀) y hy
  simpa only [g, spectralKBesselWhittaker_eq_sqrt ν q y (hY.trans_lt hy).le] using he

theorem spectralComplexSqrt_re_nonneg (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

theorem spectralComplexSqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  rw [Complex.sqrt, ← Complex.cpow_nat_mul]
  norm_num

theorem spectralNormalODE_classification (eig : ℂ) (q Y : ℝ)
    (hq : 0 < q) (hY : 0 ≤ Y) (f : ℝ → ℂ)
    (hf : ∀ t, Y < t → HasDerivAt f (deriv f t) t)
    (hf' : ∀ t, Y < t → HasDerivAt (deriv f)
      (((q : ℂ) ^ 2 - eig / (t : ℂ) ^ 2) * f t) t)
    (henergy : IntegrableOn (fun t : ℝ => ‖deriv f t‖ ^ 2) (Ioi Y))
    (hmass : IntegrableOn (fun t : ℝ => ‖f t‖ ^ 2 / t ^ 2) (Ioi Y)) :
    ∃ c : ℂ, ∀ y, Y < y → f y = c * ((Real.sqrt y : ℂ) *
      schlafliBesselK (Complex.sqrt (1 / 4 - eig)) (q * y)) := by
  have he : (1 / 4 : ℂ) - Complex.sqrt (1 / 4 - eig) ^ 2 = eig := by
    rw [spectralComplexSqrt_sq]
    ring
  apply spectralNormalODE_rightHalfPlane_classification
    (Complex.sqrt (1 / 4 - eig)) (spectralComplexSqrt_re_nonneg _) q Y hq hY f hf
  · intro t ht
    simpa only [he] using hf' t ht
  · exact henergy
  · exact hmass

end ArtinMatthews
