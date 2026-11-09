module

public import ArtinMatthews.SpectralPeterssonHeckeFourier
public import ArtinMatthews.SpectralHolomorphicCuspSeed


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine periodization of the rescaled horizontal Hecke profile.
The height Jacobian and positive additive phase are kept explicit. -/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped FourierTransform

namespace ArtinMatthews

theorem spectralPeterssonHeckeFourier_scale (f : ℝ → ℂ) (y v : ℝ) (hy : 0 < y) :
    𝓕 (fun x => f (x/y)) v = (y : ℂ)*𝓕 f (v*y) := by
  rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
  let g (t : ℝ) := Complex.exp (((-2*Real.pi*t*(v*y) : ℝ) : ℂ)*Complex.I) • f t
  have h (x : ℝ) :
      Complex.exp (((-2*Real.pi*x*v : ℝ) : ℂ)*Complex.I) • f (x/y) = g (y⁻¹*x) := by
    dsimp only [g]
    have h₁ : x/y = y⁻¹*x := by ring
    have h₂ : -2*Real.pi*x*v = -2*Real.pi*(y⁻¹*x)*(v*y) := by field_simp
    rw [h₁,h₂]
  simp_rw [h,Measure.integral_comp_inv_mul_left,abs_of_pos hy,RCLike.real_smul_eq_coe_mul]
  rfl

theorem spectralPetersson_inverseSquare_samples_summable :
    Summable (fun n : ℤ => (1+(n : ℝ)^2)⁻¹) := by
  have hs : Summable (fun n : ℤ => |(n : ℝ)|^(-(2 : ℝ))) :=
    Real.summable_abs_int_rpow (by norm_num)
  have h0 : Summable (fun n : ℤ => if n = 0 then (1 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [hn]
  apply (hs.add h0).of_nonneg_of_le (fun n => by positivity)
  intro n
  change (1+(n : ℝ)^2)⁻¹ ≤ |(n : ℝ)|^(-(2 : ℝ))+(if n=0 then 1 else 0)
  by_cases hn : n=0
  · simp [hn,Real.zero_rpow (by norm_num : -(2 : ℝ) ≠ 0)]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [ite_eq_right hn,add_zero,Real.rpow_neg (abs_nonneg _),Real.rpow_two,sq_abs]
    exact inv_anti₀ (sq_pos_of_ne_zero hnR) (by linarith)

theorem spectralPeterssonHeckeProfile_sample_bound (u lam Y y : ℝ) (n : ℤ)
    (hu : u ∈ Icc (0 : ℝ) 1) (hlam : 0 ≤ lam) (hY : 0 < Y) (hy : Y ≤ y) :
    ‖𝓕 (spectralPeterssonHeckeProfile u lam) ((n : ℝ)*y)‖ ≤
      (spectralPeterssonHeckeFourierCost lam/min 1 (Y^2))*(1+(n : ℝ)^2)⁻¹ := by
  let d := min (1 : ℝ) (Y^2)
  have hd : 0 < d := lt_min zero_lt_one (sq_pos_of_pos hY)
  have hD : d*(1+(n : ℝ)^2) ≤ 1+((n : ℝ)*y)^2 := by
    have hdy : d ≤ y^2 := (min_le_right _ _).trans (pow_le_pow_left₀ hY.le hy 2)
    have hs := mul_le_mul_of_nonneg_right hdy (sq_nonneg (n : ℝ))
    have hd1 : d ≤ 1 := min_le_left _ _
    rw [mul_add,mul_one,mul_pow]
    nlinarith only [hs,hd1]
  refine (spectralPeterssonHeckeProfile_fourier_bound u lam ((n : ℝ)*y) hu hlam).trans ?_
  change _ ≤ spectralPeterssonHeckeFourierCost lam/d*(1+(n : ℝ)^2)⁻¹
  rw [← div_eq_mul_inv,div_div]
  exact div_le_div_of_nonneg_left (spectralPeterssonHeckeFourierCost_pos hlam).le (by positivity) hD

theorem spectralPeterssonHeckeProfile_samples_summable (u lam y : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) (hlam : 0 ≤ lam) (hy : 0 < y) :
    Summable (fun n : ℤ => ‖𝓕 (spectralPeterssonHeckeProfile u lam) ((n : ℝ)*y)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => spectralPeterssonHeckeProfile_sample_bound u lam y y n hu hlam hy le_rfl)
    (spectralPetersson_inverseSquare_samples_summable.mul_left _)

theorem spectralPeterssonHeckeProfile_periodized (u lam y x : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) (hlam : 0 ≤ lam) (hy : 0 < y) :
    (∑' l : ℤ, spectralPeterssonHeckeProfile u lam ((x+(l : ℝ))/y)) =
      (y : ℂ)*(∑' n : ℤ, 𝓕 (spectralPeterssonHeckeProfile u lam) ((n : ℝ)*y)*atkinPhase ((n : ℝ)*x)) := by
  let f := spectralPeterssonHeckeProfile u lam
  let g (t : ℝ) := f (t/y)
  have hc : Continuous g := by
    have hf : Differentiable ℝ f := fun t => (spectralPeterssonHeckeProfile_hasDerivAt u lam t).differentiableAt
    exact hf.continuous.comp (continuous_id.div_const _)
  have hd : g =O[cocompact ℝ] fun t => |t|^(-(2 : ℝ)) := by
    rw [isBigO_iff]
    refine ⟨y^2,?_⟩
    filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with t ht
    have ht₀ : t ≠ 0 := fun h => ht (by simpa [h])
    change ‖f (t/y)‖ ≤ y^2*‖|t|^(-(2 : ℝ))‖
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),Real.rpow_neg (abs_nonneg _),
      Real.rpow_two,sq_abs]
    refine (spectralPeterssonHeckeProfile_norm_le u lam (t/y) hu.1 hlam).trans ?_
    have h := inv_anti₀ (sq_pos_of_ne_zero (div_ne_zero ht₀ hy.ne'))
      (show (t/y)^2 ≤ 1+(t/y)^2 by linarith)
    refine h.trans_eq ?_
    rw [div_pow,inv_div,div_eq_mul_inv]
  have hs : Summable (fun n : ℤ => 𝓕 g (n : ℝ)) := by
    simp_rw [g,spectralPeterssonHeckeFourier_scale f y _ hy]
    exact ((spectralPeterssonHeckeProfile_samples_summable u lam y hu hlam hy).of_norm).mul_left _
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc (by norm_num : 1 < (2 : ℝ)) hd hs x
  change (∑' l : ℤ, g (x+(l : ℝ))) = _
  rw [hp,← tsum_mul_left]
  apply tsum_congr
  intro n
  have hphase : fourier n (x : UnitAddCircle) = atkinPhase ((n : ℝ)*x) := by
    rw [fourier_coe_apply,atkinPhase]
    change Complex.exp (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(x : ℂ)/(1 : ℝ)) = _
    rw [Complex.ofReal_mul,Complex.ofReal_intCast,Complex.ofReal_one,div_one]
    ring_nf
  rw [hphase,show 𝓕 g (n : ℝ) = (y : ℂ)*𝓕 f ((n : ℝ)*y) from
    spectralPeterssonHeckeFourier_scale f y (n : ℝ) hy,mul_assoc]

end ArtinMatthews
