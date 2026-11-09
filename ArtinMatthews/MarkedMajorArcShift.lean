module

public import ArtinMatthews.MarkedMajorArcBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative finite contour shift with the exact triangular Perron
normalization. Its character instantiation uses the proved analytic rectangle. -/
namespace ArtinMatthews

open Complex Set MeasureTheory Erdos970

lemma marked_perron_product_finite_shift_bound {F : ℂ → ℂ} {x δ σ H B : ℝ}
    (hx : 1 ≤ x) (hδ : 0 < δ) (hδ1 : δ < 1) (hσ : 0 < σ) (hH : 0 < H)
    (hB : 0 ≤ B)
    (hres : RectangleIntegral' (fun s => F s*markedPerronKernel x s)
      (((-δ:ℝ):ℂ)-Complex.I*(H:ℂ)) ((σ:ℂ)+Complex.I*(H:ℂ)) = F 0)
    (hbound : ∀ s ∈ Rectangle
      (((-δ:ℝ):ℂ)-Complex.I*(H:ℂ)) ((σ:ℂ)+Complex.I*(H:ℂ)), ‖F s‖ ≤ B) :
    ‖(1/(2*(Real.pi:ℂ)*Complex.I))*
        VIntegral (fun s => F s*markedPerronKernel x s) σ (-H) H - F 0‖ ≤
      (2*H*(B*x^(-δ)/(δ*(1-δ))) + 2*(B*x^σ/H^2)*(σ+δ))/(2*Real.pi) := by
  have hx0 : 0 < x := by linarith
  have hab : -δ ≤ σ := by linarith
  have hm (r u : ℝ) (hr : r ∈ Icc (-δ) σ) (hu : u ∈ Icc (-H) H) :
      (r:ℂ)+(u:ℂ)*Complex.I ∈ Rectangle
        (((-δ:ℝ):ℂ)-Complex.I*(H:ℂ)) ((σ:ℂ)+Complex.I*(H:ℂ)) := by
    simpa [Rectangle,Complex.mem_reProdIm,uIcc_of_le hab,
      uIcc_of_le (show -H ≤ H by linarith)] using And.intro hr hu
  have hleft : ‖VIntegral (fun s => F s*markedPerronKernel x s) (-δ) (-H) H‖ ≤
      2*H*(B*x^(-δ)/(δ*(1-δ))) := by
    apply marked_vertical_segment_bound hH.le
    intro u hu
    rw [norm_mul]
    exact (mul_le_mul (hbound _ (hm (-δ) u ⟨le_rfl,hab⟩ hu))
      (marked_perron_kernel_left hx0 hδ hδ1 u) (norm_nonneg _) hB).trans_eq (by ring)
  have hhorizontal (u : ℝ) (hu : u = H ∨ u = -H) :
      ∀ r ∈ Icc (-δ) σ,
      ‖F ((r:ℂ)+(u:ℂ)*Complex.I)*markedPerronKernel x ((r:ℂ)+(u:ℂ)*Complex.I)‖ ≤
        B*x^σ/H^2 := by
    intro r hr
    have hu0 : u ≠ 0 := by
      rcases hu with rfl|rfl
      · exact hH.ne'
      · exact neg_ne_zero.mpr hH.ne'
    have huI : u ∈ Icc (-H) H := by rcases hu with rfl|rfl <;> constructor <;> linarith
    have husq : u^2=H^2 := by rcases hu with rfl|rfl <;> ring
    rw [norm_mul]
    have hk := marked_perron_kernel_horizontal hx0 r hu0
    rw [husq] at hk
    calc
      _ ≤ B*(x^r/H^2) := mul_le_mul (hbound _ (hm r u hr huI)) hk (norm_nonneg _) hB
      _ ≤ B*(x^σ/H^2) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx hr.2) (sq_nonneg H)) hB
      _ = _ := by ring
  have hh := marked_rectangle_pole_shift_bound hab hres
    (hhorizontal H (Or.inl rfl)) (hhorizontal (-H) (Or.inr rfl))
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2*Real.pi)
  simpa only [sub_neg_eq_add] using add_le_add hleft (le_refl (2*(B*x^σ/H^2)*(σ+δ)))

end ArtinMatthews
