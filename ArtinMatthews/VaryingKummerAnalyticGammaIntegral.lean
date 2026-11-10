module

public import ArtinMatthews.VaryingKummerAnalyticMellin
public import Mathlib.Algebra.Ring.IsFormallyReal


set_option backward.privateInPublic true
@[expose] public section

/-! Exact generic Gamma/Mellin proofs from OpenAI
PrimePackets/ZeroReflection.lean, from `logGammaKernel` through `prod_abs_cpow`.
Only namespace and imports are changed. No number-field signature is assumed. -/
namespace ArtinMatthews.ReusedArchMellin
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal
noncomputable section
def logGammaKernel (s : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (s * (x : ℂ) - (Real.exp x : ℂ))

lemma logGammaKernel_eq (s : ℂ) (x : ℝ) :
    logGammaKernel s x = Real.exp x •
      ((Real.exp (-Real.exp x) : ℂ) * (Real.exp x : ℂ) ^ (s-1)) := by
  rw [Complex.real_smul, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [logGammaKernel, Complex.ofReal_exp, Complex.ofReal_neg]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

lemma integrable_logGammaKernel {s : ℂ} (hs : 0 < s.re) :
    Integrable (logGammaKernel s) := by
  have H := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (s-1))
  simp only [Set.image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    ← logGammaKernel_eq, integrableOn_univ] at H
  exact H.mp (Complex.GammaIntegral_convergent hs)

lemma integral_logGammaKernel {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ, logGammaKernel s x) = Complex.Gamma s := by
  have H := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (s-1))
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  simpa only [Set.image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _),
    ← logGammaKernel_eq, Measure.restrict_univ] using H.symm

 
def gaussianLogKernel (s : ℂ) (r x : ℝ) : ℂ :=
  Complex.exp (s * (x : ℂ) - (r * Real.exp (2*x) : ℝ))

lemma gaussianLogKernel_eq {r : ℝ} (hr : 0 < r) (s : ℂ) (x : ℝ) :
    gaussianLogKernel s r x = (r : ℂ) ^ (-(s/2)) *
      logGammaKernel (s/2) (2*x + Real.log r) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    ← Complex.ofReal_log hr.le, logGammaKernel, ← Complex.exp_add,
    Real.exp_add, Real.exp_log hr]
  simp only [gaussianLogKernel, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  congr 1
  ring

lemma integrable_gaussianLogKernel {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    Integrable (gaussianLogKernel s r) := by
  have ha : 0 < (s/2).re := by simpa using half_pos hs
  have H := ((integrable_logGammaKernel ha).comp_add_right (Real.log r)).comp_mul_left'
    (R := (2 : ℝ)) (by norm_num)
  simpa only [← gaussianLogKernel_eq hr] using H.const_mul ((r : ℂ)^(-(s/2)))

lemma integral_gaussianLogKernel {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ, gaussianLogKernel s r x) =
      (1/2 : ℂ) * (r : ℂ) ^ (-(s/2)) * Complex.Gamma (s/2) := by
  have ha : 0 < (s/2).re := by simpa using half_pos hs
  simp_rw [gaussianLogKernel_eq hr]
  rw [integral_const_mul, Measure.integral_comp_mul_left
      (fun x => logGammaKernel (s/2) (x + Real.log r)) 2,
    integral_add_right_eq_self, integral_logGammaKernel ha]
  norm_num [Complex.real_smul]
  ring

lemma continuous_gaussianLogKernel (s : ℂ) (r : ℝ) :
    Continuous (gaussianLogKernel s r) := by
  unfold gaussianLogKernel
  fun_prop

 
lemma integral_gaussianLogKernel_product (n : ℕ) {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) :
    (∫ x : Fin n → ℝ, ∏ i, gaussianLogKernel s r (x i)) =
      ((1/2 : ℂ) * (r : ℂ)^(-(s/2)) * Complex.Gamma (s/2)) ^ n := by
  rw [integral_fintype_prod_volume_eq_pow, Fintype.card_fin, integral_gaussianLogKernel hs hr]

lemma integrable_gaussianLogKernel_product (n : ℕ) {s : ℂ} (hs : 0 < s.re)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : Fin n → ℝ => ∏ i, gaussianLogKernel s r (x i)) :=
  Integrable.fintype_prod (fun _ => integrable_gaussianLogKernel hs hr)

lemma exp_two_mul (x : ℝ) : Real.exp (2*x) = (Real.exp x)^2 := by
  rw [show 2*x = x+x by ring, Real.exp_add, pow_two]

lemma scaled_cpow {r a : ℝ} (hr : 0 < r) (ha : a ≠ 0) (s : ℂ) :
    ((r*a^2 : ℝ) : ℂ)^(-(s/2)) = (r : ℂ)^(-(s/2)) * ((|a| : ℝ) : ℂ)^(-s) := by
  have hsq : 0 < a^2 := sq_pos_of_ne_zero ha
  have hab : 0 < |a| := abs_pos.mpr ha
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos hr hsq).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hab.ne'),
    ← Complex.exp_add, ← Complex.ofReal_log (mul_pos hr hsq).le,
    ← Complex.ofReal_log hr.le, ← Complex.ofReal_log hab.le,
    Real.log_mul hr.ne' (pow_ne_zero _ ha), Real.log_pow, Real.log_abs]
  push_cast
  congr 1
  ring

lemma gaussianLogKernel_scale (s : ℂ) (r a x : ℝ) :
    gaussianLogKernel s (r*a^2) x =
      Complex.exp (s*(x : ℂ) - (r*(a*Real.exp x)^2 : ℝ)) := by
  rw [gaussianLogKernel, exp_two_mul]
  congr 2
  push_cast
  ring

lemma integral_scaled_gaussianLogKernel {s : ℂ} (hs : 0 < s.re)
    {r a : ℝ} (hr : 0 < r) (ha : a ≠ 0) :
    (∫ x : ℝ, Complex.exp (s*(x : ℂ) - (r*(a*Real.exp x)^2 : ℝ))) =
      ((1/2 : ℂ) * (r : ℂ)^(-(s/2)) * Complex.Gamma (s/2)) * ((|a| : ℝ) : ℂ)^(-s) := by
  simp_rw [← gaussianLogKernel_scale]
  rw [integral_gaussianLogKernel hs (mul_pos hr (sq_pos_of_ne_zero ha))]
  rw [scaled_cpow hr ha]
  ring

lemma prod_abs_cpow {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) (s : ℂ) :
    (∏ i, ((|a i| : ℝ) : ℂ)^s) = ((∏ i, |a i| : ℝ) : ℂ)^s := by
  have hp : 0 < ∏ i, |a i| := Finset.prod_pos (fun i _ => abs_pos.mpr (ha i))
  have H (i : ι) : ((|a i| : ℝ) : ℂ)^s = Complex.exp ((Real.log |a i| : ℂ)*s) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (ha i))),
      ← Complex.ofReal_log (abs_nonneg _)]
  simp_rw [H]
  rw [← Complex.exp_sum,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le, Real.log_prod (fun i _ => abs_ne_zero.mpr (ha i)),
    Complex.ofReal_sum, Finset.sum_mul]


end
end ArtinMatthews.ReusedArchMellin
