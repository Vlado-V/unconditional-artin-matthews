module

public import ArtinMatthews.MarkedMajorArcContour


set_option backward.privateInPublic true
@[expose] public section

/-! Finite rectangle and power-tail estimates extracted from the actual
MRT contour proofs, applied to the triangular Perron kernel. -/
namespace ArtinMatthews

open Complex Set MeasureTheory Erdos970 intervalIntegral

lemma marked_power_integral_tail {f : ℝ → ℂ} {T D a : ℝ}
    (hT : 0 < T) (ha : 1 < a)
    (hbound : ∀ t ∈ Ioi T, ‖f t‖ ≤ D * t ^ (-a)) :
    ‖∫ t in Ioi T, f t‖ ≤ D * T ^ (1 - a) / (a - 1) := by
  have hi : IntegrableOn (fun t : ℝ => D * t ^ (-a)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -a < -1) hT).const_mul D
  have he : (∫ t in Ioi T, D * t ^ (-a)) = D * T ^ (1 - a) / (a - 1) := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -a < -1) hT]
    rw [show -a + 1 = 1 - a by ring]
    rw [show 1 - a = -(a - 1) by ring]
    simp only [div_neg]
    ring
  exact (norm_integral_le_of_norm_le hi
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact hbound t ht)).trans_eq he

lemma marked_rectangle_pole_shift_bound {f : ℂ → ℂ} {a b T B : ℝ} {A : ℂ}
    (hab : a ≤ b)
    (hres : RectangleIntegral' f ((a : ℂ) - Complex.I * (T : ℂ))
      ((b : ℂ) + Complex.I * (T : ℂ)) = A)
    (hup : ∀ σ ∈ Icc a b, ‖f ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ B)
    (hdown : ∀ σ ∈ Icc a b, ‖f ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ B) :
    ‖(1 / (2 * (Real.pi : ℂ) * Complex.I)) * VIntegral f b (-T) T - A‖ ≤
      (‖VIntegral f a (-T) T‖ + 2 * B * (b - a)) / (2 * Real.pi) := by
  have htop : ‖HIntegral f a b T‖ ≤ B * (b - a) := by
    have hp : ∀ σ ∈ uIoc a b, ‖f ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ B := by
      intro σ hσ
      exact hup σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ))
    simpa only [HIntegral, abs_of_nonneg (sub_nonneg.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hp
  have hbot : ‖HIntegral f a b (-T)‖ ≤ B * (b - a) := by
    have hp : ∀ σ ∈ uIoc a b, ‖f ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ B := by
      intro σ hσ
      exact hdown σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ))
    simpa only [HIntegral, abs_of_nonneg (sub_nonneg.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hp
  have hid : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * VIntegral f b (-T) T - A =
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (VIntegral f a (-T) T + HIntegral f a b T - HIntegral f a b (-T)) := by
    rw [← hres]
    simp only [RectangleIntegral', RectangleIntegral, smul_eq_mul, Complex.sub_re,
      Complex.add_re, Complex.sub_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, one_mul, zero_sub, sub_zero, add_zero, zero_add]
    ring
  rw [hid, norm_mul]
  have hn : ‖1 / (2 * (Real.pi : ℂ) * Complex.I)‖ = 1 / (2 * Real.pi) := by
    simp [Complex.norm_real, Real.norm_eq_abs]
  rw [hn]
  have hm : ‖VIntegral f a (-T) T + HIntegral f a b T - HIntegral f a b (-T)‖ ≤
      ‖VIntegral f a (-T) T‖ + 2 * B * (b - a) := by
    exact (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans (by linarith))
  calc
    _ ≤ (1 / (2 * Real.pi)) * (‖VIntegral f a (-T) T‖ + 2 * B * (b - a)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring


lemma marked_vertical_power_tails {f : ℂ → ℂ} {b T D a : ℝ}
    (hT : 0 < T) (ha : 1 < a)
    (hf : Integrable (fun t : ℝ => f ((b : ℂ) + (t : ℂ) * Complex.I)))
    (hbound : ∀ t : ℝ, T ≤ |t| →
      ‖f ((b : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D * |t| ^ (-a)) :
    ‖VerticalIntegral f b - VIntegral f b (-T) T‖ ≤
      2 * D * T ^ (1 - a) / (a - 1) := by
  have hu : ‖∫ t in Ioi T, f ((b : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      D * T ^ (1 - a) / (a - 1) := by
    apply marked_power_integral_tail hT ha
    intro t ht
    simpa only [abs_of_pos (hT.trans ht)] using hbound t
      (by rw [abs_of_pos (hT.trans ht)]; exact ht.le)
  have hd : ‖∫ t in Iic (-T), f ((b : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      D * T ^ (1 - a) / (a - 1) := by
    rw [← integral_comp_neg_Ioi T]
    apply marked_power_integral_tail hT ha
    intro t ht
    simpa only [abs_neg, abs_of_pos (hT.trans ht)] using hbound (-t)
      (by rw [abs_neg, abs_of_pos (hT.trans ht)]; exact ht.le)
  rw [verticalIntegral_split_three (-T) T hf]
  have he (x y z : ℂ) : x + y + z - y = x + z := by ring
  rw [he]
  calc
    _ ≤ ‖Complex.I • (∫ t in Iic (-T), f ((b : ℂ) + (t : ℂ) * Complex.I))‖ +
        ‖Complex.I • (∫ t in Ici T, f ((b : ℂ) + (t : ℂ) * Complex.I))‖ := norm_add_le _ _
    _ = ‖∫ t in Iic (-T), f ((b : ℂ) + (t : ℂ) * Complex.I)‖ +
        ‖∫ t in Ioi T, f ((b : ℂ) + (t : ℂ) * Complex.I)‖ := by
      rw [norm_smul, norm_smul, norm_I, one_mul, one_mul, integral_Ici_eq_integral_Ioi]
    _ ≤ D * T ^ (1 - a) / (a - 1) + D * T ^ (1 - a) / (a - 1) := add_le_add hd hu
    _ = _ := by ring


lemma marked_perron_denominator_horizontal (σ t : ℝ) :
    t ^ 2 ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) *
      ((σ : ℂ) + (t : ℂ) * Complex.I + 1)‖ := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have h1 : |t| ≤ ‖z‖ := by simpa [z] using Complex.abs_im_le_norm z
  have h2 : |t| ≤ ‖z + 1‖ := by simpa [z] using Complex.abs_im_le_norm (z + 1)
  have hm := mul_le_mul h1 h2 (abs_nonneg t) (norm_nonneg z)
  simpa only [← sq, sq_abs, norm_mul] using hm


lemma marked_perron_kernel_horizontal {x : ℝ} (hx : 0 < x) (σ : ℝ)
    {t : ℝ} (ht : t ≠ 0) :
    ‖markedPerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ x ^ σ / t ^ 2 := by
  rw [markedPerronKernel, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (sq_pos_of_ne_zero ht)
    (marked_perron_denominator_horizontal σ t)


lemma marked_perron_kernel_left {x δ : ℝ} (hx : 0 < x)
    (hδ : 0 < δ) (hδ1 : δ < 1) (t : ℝ) :
    ‖markedPerronKernel x (((-δ:ℝ):ℂ)+(t:ℂ)*Complex.I)‖ ≤
      x^(-δ)/(δ*(1-δ)) := by
  let z : ℂ := ((-δ:ℝ):ℂ)+(t:ℂ)*Complex.I
  have h1 : δ ≤ ‖z‖ := by
    simpa [z,abs_of_nonneg hδ.le] using Complex.abs_re_le_norm z
  have h2 : 1-δ ≤ ‖z+1‖ := by
    have hh := Complex.abs_re_le_norm (z+1)
    simpa [z,show -δ+1=1-δ by ring,abs_of_pos (sub_pos.mpr hδ1)] using hh
  have hm := mul_le_mul h1 h2 (by linarith : 0≤1-δ) (norm_nonneg z)
  rw [markedPerronKernel,norm_div,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero]
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (by positivity)
  simpa only [norm_mul] using hm

lemma marked_vertical_segment_bound {f : ℂ → ℂ} {a H B : ℝ} (hH : 0 ≤ H)
    (hf : ∀ t ∈ Icc (-H) H, ‖f ((a:ℂ)+(t:ℂ)*Complex.I)‖ ≤ B) :
    ‖VIntegral f a (-H) H‖ ≤ 2*H*B := by
  have hh : ∀ t ∈ uIoc (-H) H, ‖f ((a:ℂ)+(t:ℂ)*Complex.I)‖ ≤ B := by
    intro t ht
    apply hf t
    exact Ioc_subset_Icc_self (by simpa [uIoc_of_le (show -H ≤ H by linarith)] using ht)
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const hh
  calc
    _ = ‖∫ u in -H..H, f ((a:ℂ)+(u:ℂ)*Complex.I)‖ := by simp [VIntegral]
    _ ≤ B*|H- -H| := hn
    _ = 2*H*B := by rw [abs_of_nonneg (by linarith : 0≤H- -H)]; ring


end ArtinMatthews
