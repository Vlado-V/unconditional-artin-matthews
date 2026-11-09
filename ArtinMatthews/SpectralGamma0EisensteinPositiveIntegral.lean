module

public import ArtinMatthews.SpectralGamma0EisensteinPositiveSum
public import ArtinMatthews.SpectralGamma0EisensteinIntegralExchange


set_option backward.privateInPublic true
@[expose] public section

/-! The actual constant-term integral with its literal signed-row normalization removed. -/
noncomputable section
open Set MeasureTheory
namespace ArtinMatthews

theorem gamma0EisensteinPrimitiveTerm_horizontal_integrable (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) (v : Gamma0EisensteinPrimitiveRows N) :
    IntegrableOn (fun x => gamma0EisensteinPrimitiveTerm N s v (gamma0EisensteinHorizontalPoint y hy x))
      (Ioc (0:ℝ) 1) := by
  let e := gamma0EisensteinPrimitiveEquiv N
  have he : (fun x => gamma0EisensteinPrimitiveTerm N s v (gamma0EisensteinHorizontalPoint y hy x)) =
      fun x => gamma0EisensteinSummand N s (e.symm v) (gamma0EisensteinHorizontalPoint y hy x) := by
    funext x
    rw [← gamma0EisensteinPrimitiveTerm_eq,e.apply_symm_apply]
  rw [he]
  exact gamma0EisensteinSummand_horizontal_integrable N s hs y hy _

theorem gamma0EisensteinPrimitiveTerm_integral_norm_summable (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) :
    Summable (fun v : Gamma0EisensteinPrimitiveRows N => ∫ x in Ioc (0:ℝ) 1,
      ‖gamma0EisensteinPrimitiveTerm N s v (gamma0EisensteinHorizontalPoint y hy x)‖) := by
  apply (gamma0EisensteinPrimitiveEquiv N).summable_iff.mp
  change Summable (fun v : Gamma0EisensteinRows N => ∫ x in Ioc (0:ℝ) 1,
    ‖gamma0EisensteinPrimitiveTerm N s (gamma0EisensteinPrimitiveEquiv N v)
      (gamma0EisensteinHorizontalPoint y hy x)‖)
  simpa only [gamma0EisensteinPrimitiveTerm_eq] using
    gamma0EisensteinSummand_integral_norm_summable N s hs y hy

theorem gamma0EisensteinPrimitiveTerm_integral_summable (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) :
    Summable (fun v : Gamma0EisensteinPrimitiveRows N => ∫ x in Ioc (0:ℝ) 1,
      gamma0EisensteinPrimitiveTerm N s v (gamma0EisensteinHorizontalPoint y hy x)) := by
  exact (gamma0EisensteinPrimitiveTerm_integral_norm_summable N s hs y hy).of_norm_bounded
    (f := fun v : Gamma0EisensteinPrimitiveRows N => ∫ x in Ioc (0:ℝ) 1,
      gamma0EisensteinPrimitiveTerm N s v (gamma0EisensteinHorizontalPoint y hy x))
    (fun v => norm_integral_le_integral_norm _)

theorem gamma0EisensteinPositiveTerm_integral_summable (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) :
    Summable (fun v : Gamma0EisensteinPositiveRows N => ∫ x in Ioc (0:ℝ) 1,
      gamma0EisensteinPrimitiveTerm N s v.val (gamma0EisensteinHorizontalPoint y hy x)) :=
  (gamma0EisensteinPrimitiveTerm_integral_summable N s hs y hy).comp_injective
    (i := fun v : Gamma0EisensteinPositiveRows N => v.val) Subtype.coe_injective

theorem gamma0Eisenstein_integral_eq_positive_rows (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) :
    (∫ x in (0:ℝ)..1, gamma0EisensteinSlice N s y hy x) = (y:ℂ)^s+
      ∑' v : Gamma0EisensteinPositiveRows N, ∫ x in Ioc (0:ℝ) 1,
        gamma0EisensteinPrimitiveTerm N s v.val (gamma0EisensteinHorizontalPoint y hy x) := by
  rw [gamma0Eisenstein_integral_eq_half_tsum_rows N s hs y hy]
  have he : (∑' v : Gamma0EisensteinRows N, ∫ x in (0:ℝ)..1,
      gamma0EisensteinSummand N s v (gamma0EisensteinHorizontalPoint y hy x)) =
      ∑' v : Gamma0EisensteinPrimitiveRows N, ∫ x in Ioc (0:ℝ) 1,
        gamma0EisensteinPrimitiveTerm N s v (gamma0EisensteinHorizontalPoint y hy x) := by
    simpa only [gamma0EisensteinPrimitiveTerm_eq,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using
      (gamma0EisensteinPrimitiveEquiv N).tsum_eq (fun v => ∫ x in Ioc (0:ℝ) 1,
        gamma0EisensteinPrimitiveTerm N s v (gamma0EisensteinHorizontalPoint y hy x))
  rw [he,gamma0Eisenstein_signed_tsum N _ (gamma0EisensteinPrimitiveTerm_integral_summable N s hs y hy)
    (fun v => by simp only [gamma0EisensteinPrimitiveTerm_neg])]
  simp only [gamma0EisensteinPrimitiveTerm_zero]
  change (1/2:ℂ)*((∫ _x in Ioc (0:ℝ) 1, (y:ℂ)^s)+
    (∫ _x in Ioc (0:ℝ) 1, (y:ℂ)^s)+2*(∑' v : Gamma0EisensteinPositiveRows N,
      ∫ x in Ioc (0:ℝ) 1, gamma0EisensteinPrimitiveTerm N s v.val
        (gamma0EisensteinHorizontalPoint y hy x)))=_
  simp
  ring

end ArtinMatthews
