module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The literal dx/x moment at exponent five eighths follows from
the small-argument and large-argument envelopes of the folded kernel. -/
namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

theorem elliptic_five_eighths_moment (G : ℝ → ℂ) (hG : Measurable G) (C : ℝ) (hC : 0 ≤ C)
    (hsmall : ∀ x : ℝ, 0 < x → x ≤ 1 → ‖G x‖ ≤ C*x^(3/4 : ℝ))
    (hlarge : ∀ x : ℝ, 1 ≤ x → ‖G x‖ ≤ C/x^2) :
    IntegrableOn (fun x : ℝ => x^(-5/8 : ℝ)*‖G x‖/x) (Ioi 0) ∧
      (∫ x : ℝ in Ioi 0, x^(-5/8 : ℝ)*‖G x‖/x) ≤ C*(8+8/21) := by
  let w : ℝ → ℝ := fun x => x^(-5/8 : ℝ)*‖G x‖/x
  have hwm : Measurable w := by dsimp only [w]; fun_prop
  have hw0 (x : ℝ) (hx : 0 < x) : 0 ≤ w x := by
    dsimp only [w]
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (norm_nonneg _)) hx.le
  have hsmall' (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) : w x ≤ C*x^(-7/8 : ℝ) := by
    calc
      _ ≤ x^(-5/8 : ℝ)*(C*x^(3/4 : ℝ))/x :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hsmall x hx.1 hx.2) (Real.rpow_nonneg hx.1.le _)) hx.1.le
      _ = C*(x^(-5/8 : ℝ)*x^(3/4 : ℝ)/x^(1 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = C*x^(-7/8 : ℝ) := by
        rw [← Real.rpow_add hx.1, ← Real.rpow_sub hx.1]
        norm_num
  have hlarge' (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) : w x ≤ C*x^(-29/8 : ℝ) := by
    have hx0 : 0 < x := zero_lt_one.trans hx
    calc
      _ ≤ x^(-5/8 : ℝ)*(C/x^2)/x :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hlarge x hx.le) (Real.rpow_nonneg hx0.le _)) hx0.le
      _ = C*(x^(-5/8 : ℝ)/x^(2 : ℝ)/x^(1 : ℝ)) := by rw [Real.rpow_two, Real.rpow_one]; ring
      _ = C*x^(-29/8 : ℝ) := by
        rw [← Real.rpow_sub hx0, ← Real.rpow_sub hx0]
        norm_num
  have hnear : IntegrableOn (fun x : ℝ => C*x^(-7/8 : ℝ)) (Ioc 0 1) := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
      (by norm_num : (-1 : ℝ) < -7/8))
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h).const_mul C
  have hfar : IntegrableOn (fun x : ℝ => C*x^(-29/8 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-29/8 : ℝ) < -1) zero_lt_one).const_mul C
  have hwn : IntegrableOn w (Ioc 0 1) := by
    apply Integrable.mono hnear hwm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x hx.1), Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg hx.1.le _))]
    exact hsmall' x hx
  have hwf : IntegrableOn w (Ioi 1) := by
    apply Integrable.mono hfar hwm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x (zero_lt_one.trans hx)), Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (zero_lt_one.trans hx).le _))]
    exact hlarge' x hx
  have hwu : IntegrableOn w (Ioi 0) := by
    have h := hwn.union hwf
    rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at h
  refine ⟨hwu, ?_⟩
  have hnearIntegral : (∫ x : ℝ in Ioc 0 1, C*x^(-7/8 : ℝ)) = C*8 := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -7/8))]
    norm_num
  have hfarIntegral : (∫ x : ℝ in Ioi 1, C*x^(-29/8 : ℝ)) = C*(8/21) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-29/8 : ℝ) < -1) zero_lt_one]
    norm_num
  change (∫ x in Ioi (0 : ℝ), w x) ≤ _
  rw [← Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hwn hwf]
  calc
    _ ≤ (∫ x : ℝ in Ioc 0 1, C*x^(-7/8 : ℝ))+
        ∫ x : ℝ in Ioi 1, C*x^(-29/8 : ℝ) :=
      add_le_add (setIntegral_mono_on hwn hnear measurableSet_Ioc hsmall')
        (setIntegral_mono_on hwf hfar measurableSet_Ioi hlarge')
    _ = _ := by rw [hnearIntegral, hfarIntegral]; ring

end
end ArtinMatthews
