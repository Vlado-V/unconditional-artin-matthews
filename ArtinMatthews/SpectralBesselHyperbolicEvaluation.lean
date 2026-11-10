module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralBesselKConvergence
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine Schläfli K function in logarithmic hyperbolic coordinates.
The substitution and absolute convergence hold for every complex order. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem positive_exp_scale_image {a : ℝ} (ha : 0 < a) :
    (fun u : ℝ => a*Real.exp u) '' univ = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨u,_,rfl⟩
    exact mul_pos ha (Real.exp_pos u)
  · intro ht
    refine ⟨Real.log (t/a),mem_univ _,?_⟩
    dsimp only
    rw [Real.exp_log (div_pos ht ha)]
    field_simp [ha.ne']

theorem positive_exp_scale_injective {a : ℝ} (ha : 0 < a) :
    Function.Injective (fun u : ℝ => a*Real.exp u) := by
  intro u v h
  exact Real.exp_injective (mul_left_cancel₀ ha.ne' h)

theorem positive_exp_scale_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (F : ℝ → E) :
    (∫ t in Ioi (0 : ℝ), F t) = ∫ u : ℝ, (a*Real.exp u) • F (a*Real.exp u) := by
  rw [← positive_exp_scale_image ha]
  rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun u _ => ((Real.hasDerivAt_exp u).const_mul a).hasDerivWithinAt)
    (positive_exp_scale_injective ha).injOn]
  simp only [Measure.restrict_univ,abs_of_pos (mul_pos ha (Real.exp_pos _))]

theorem positive_exp_scale_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 < a) (F : ℝ → E) :
    IntegrableOn F (Ioi (0 : ℝ)) ↔
      Integrable (fun u : ℝ => (a*Real.exp u) • F (a*Real.exp u)) := by
  rw [← positive_exp_scale_image ha]
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun u _ => ((Real.hasDerivAt_exp u).const_mul a).hasDerivWithinAt)
    (positive_exp_scale_injective ha).injOn]
  simp only [integrableOn_univ,abs_of_pos (mul_pos ha (Real.exp_pos _))]

def spectralKLogKernel (ν : ℂ) (x u : ℝ) : ℂ :=
  Complex.exp ((-(x*Real.cosh u) : ℝ) + ν*(u : ℂ))

theorem schlafli_log_kernel (ν : ℂ) {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ((1/2 : ℂ)*(x/2 : ℂ)^(-ν)) *
      ((x/2*Real.exp u) • (((x/2*Real.exp u : ℝ) : ℂ)^(ν-1) *
        Complex.exp (-((x/2*Real.exp u : ℝ) : ℂ)-(x : ℂ)^2/(4*(x/2*Real.exp u))))) =
      (1/2 : ℂ)*spectralKLogKernel ν x u := by
  let a : ℝ := x/2
  let t : ℝ := a*Real.exp u
  have ha : 0 < a := div_pos hx (by norm_num)
  have ht : 0 < t := mul_pos ha (Real.exp_pos u)
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  suffices H : ((1/2 : ℂ)*(a : ℂ)^(-ν)) *
      ((t : ℝ) • ((t : ℂ)^(ν-1)*Complex.exp (-(t : ℂ)-(x : ℂ)^2/(4*t)))) =
        (1/2 : ℂ)*spectralKLogKernel ν x u by
    simpa only [t,a,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat] using H
  have hp : (t : ℂ)*(t : ℂ)^(ν-1) = (t : ℂ)^ν := by
    calc
      _ = (t : ℂ)^(1 : ℂ)*(t : ℂ)^(ν-1) := by rw [Complex.cpow_one]
      _ = (t : ℂ)^(1+(ν-1)) := (Complex.cpow_add _ _ htC).symm
      _ = _ := by congr 1; ring
  have hepow : (Real.exp u : ℂ)^ν = Complex.exp ((u : ℂ)*ν) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le,Real.log_exp]
  have htPow : (t : ℂ)^ν = (a : ℂ)^ν*Complex.exp ((u : ℂ)*ν) := by
    dsimp [t]
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg ha.le (Real.exp_pos u).le,hepow]
  have haPow : (a : ℂ)^(-ν)*(a : ℂ)^ν = 1 := by
    rw [← Complex.cpow_add (-ν) ν haC,neg_add_cancel,Complex.cpow_zero]
  have hexp : -(t : ℂ)-(x : ℂ)^2/(4*t) = (-(x*Real.cosh u) : ℝ) := by
    have hr : -t-x^2/(4*t) = -(x*Real.cosh u) := by
      dsimp [t,a]
      rw [Real.cosh_eq,Real.exp_neg]
      field_simp [hx.ne',(Real.exp_pos u).ne']
      ring
    exact_mod_cast hr
  rw [Complex.real_smul,← mul_assoc (t : ℂ),hp,htPow,hexp]
  unfold spectralKLogKernel
  rw [Complex.exp_add]
  calc
    _ = (1/2 : ℂ)*((a : ℂ)^(-ν)*(a : ℂ)^ν)*
        (Complex.exp ((u : ℂ)*ν)*Complex.exp (-(x*Real.cosh u) : ℝ)) := by ring
    _ = _ := by rw [haPow]; ring

theorem schlafliBesselK_hyperbolic_integral (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    OAI.CubicEisenstein.schlafliBesselK ν x =
      (1/2 : ℂ)*∫ u : ℝ, spectralKLogKernel ν x u := by
  unfold OAI.CubicEisenstein.schlafliBesselK OAI.CubicEisenstein.schlafliIntegral
  rw [positive_exp_scale_integral (a := x/2) (div_pos hx (by norm_num)),← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  simpa only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat] using schlafli_log_kernel ν hx u

theorem spectralKLogKernel_integrable (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    Integrable (spectralKLogKernel ν x) := by
  have ht := (positive_exp_scale_integrable (a := x/2) (div_pos hx (by norm_num))
    (fun t : ℝ => (t : ℂ)^(ν-1)*Complex.exp (-(t : ℂ)-(x : ℂ)^2/(4*t)))).mp
      (schlafliIntegral_integrable_all_orders ν x hx)
  have hp := ht.const_mul ((1/2 : ℂ)*(x/2 : ℂ)^(-ν))
  have hh : Integrable (fun u => (1/2 : ℂ)*spectralKLogKernel ν x u) := by
    apply hp.congr
    filter_upwards [] with u
    simpa only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat] using schlafli_log_kernel ν hx u
  convert hh.const_mul (2 : ℂ) using 1
  ext u
  ring

end ArtinMatthews
