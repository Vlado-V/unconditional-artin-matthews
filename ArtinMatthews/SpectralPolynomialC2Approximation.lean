module

public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform approximation of two derivatives by matching the value and slope at zero. -/
namespace ArtinMatthews
open scoped Polynomial
open Set Polynomial
noncomputable section

theorem exists_complexPolynomial_near_continuousOn
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ u ∈ Icc (0 : ℝ) 1, ‖p.eval (u : ℂ) - f u‖ < ε := by
  obtain ⟨r, hr⟩ := exists_polynomial_near_of_continuousOn 0 1
    (fun u => (f u).re) (Complex.continuous_re.comp_continuousOn hf) (ε / 2) (by linarith)
  obtain ⟨i, hi⟩ := exists_polynomial_near_of_continuousOn 0 1
    (fun u => (f u).im) (Complex.continuous_im.comp_continuousOn hf) (ε / 2) (by linarith)
  let p := r.map Complex.ofRealHom + C Complex.I * i.map Complex.ofRealHom
  refine ⟨p, ?_⟩
  intro u hu
  have hp : p.eval (u : ℂ) = ((r.eval u : ℝ) : ℂ) + ((i.eval u : ℝ) : ℂ) * Complex.I := by
    have hrEval := eval_map_apply (p := r) Complex.ofRealHom u
    have hiEval := eval_map_apply (p := i) Complex.ofRealHom u
    change (r.map Complex.ofRealHom).eval (u : ℂ) = ((r.eval u : ℝ) : ℂ) at hrEval
    change (i.map Complex.ofRealHom).eval (u : ℂ) = ((i.eval u : ℝ) : ℂ) at hiEval
    simp only [p, eval_add, eval_mul, eval_C, hrEval, hiEval, mul_comm]
  have he : p.eval (u : ℂ) - f u =
      ((r.eval u - (f u).re : ℝ) : ℂ) + ((i.eval u - (f u).im : ℝ) : ℂ) * Complex.I := by
    calc
      _ = (((r.eval u : ℝ) : ℂ) + ((i.eval u : ℝ) : ℂ) * Complex.I) -
          (((f u).re : ℂ) + ((f u).im : ℂ) * Complex.I) := by
        rw [hp, Complex.re_add_im]
      _ = _ := by push_cast; ring
  rw [he]
  refine (norm_add_le _ _).trans_lt ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  linarith [hr u hu, hi u hu]

private def polynomialPrimitiveZero (p : ℂ[X]) : ℂ[X] :=
  p.sum fun n a => monomial (n + 1) (a / ((n : ℂ) + 1))

private theorem polynomialPrimitiveZero_derivative (p : ℂ[X]) :
    (polynomialPrimitiveZero p).derivative = p := by
  classical
  unfold polynomialPrimitiveZero
  change (∑ n ∈ p.support, monomial (n + 1) (p.coeff n / ((n : ℂ) + 1))).derivative = p
  rw [derivative_sum]
  calc
    _ = ∑ n ∈ p.support, monomial n (p.coeff n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [derivative_monomial_succ, div_mul_cancel₀]
      exact_mod_cast Nat.succ_ne_zero n
    _ = p := sum_monomial_eq p

private theorem polynomialPrimitiveZero_eval_zero (p : ℂ[X]) :
    (polynomialPrimitiveZero p).eval 0 = 0 := by
  classical
  unfold polynomialPrimitiveZero
  rw [Polynomial.eval_sum]
  unfold Polynomial.sum
  apply Finset.sum_eq_zero
  intro n _
  dsimp only
  rw [eval_monomial, zero_pow (Nat.succ_ne_zero n), mul_zero]

theorem exists_complexPolynomial_C2_near
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ u ∈ Icc (0 : ℝ) 1,
      ‖p.eval (u : ℂ) - f u‖ ≤ ε ∧
      ‖p.derivative.eval (u : ℂ) - deriv f u‖ ≤ ε ∧
      ‖p.derivative.derivative.eval (u : ℂ) - deriv (deriv f) u‖ ≤ ε := by
  have hf₁ : ContDiff ℝ 1 (deriv f) := hf.deriv'
  obtain ⟨q, hq⟩ := exists_complexPolynomial_near_continuousOn (deriv (deriv f))
    hf₁.continuous_deriv_one.continuousOn hε
  let a := C (deriv f 0) + polynomialPrimitiveZero q
  let p := C (f 0) + polynomialPrimitiveZero a
  have haD : a.derivative = q := by simp only [a, derivative_add, derivative_C,
    polynomialPrimitiveZero_derivative, zero_add]
  have hpD : p.derivative = a := by simp only [p, derivative_add, derivative_C,
    polynomialPrimitiveZero_derivative, zero_add]
  have ha0 : a.eval 0 = deriv f 0 := by simp only [a, eval_add, eval_C,
    polynomialPrimitiveZero_eval_zero, add_zero]
  have hp0 : p.eval 0 = f 0 := by simp only [p, eval_add, eval_C,
    polynomialPrimitiveZero_eval_zero, add_zero]
  have ha' (u : ℝ) : HasDerivAt (fun t : ℝ => a.eval (t : ℂ) - deriv f t)
      (q.eval (u : ℂ) - deriv (deriv f) u) u := by
    rw [← haD]
    exact (a.hasDerivAt (u : ℂ)).comp_ofReal.sub (hf.differentiable_deriv_two u).hasDerivAt
  have hp' (u : ℝ) : HasDerivAt (fun t : ℝ => p.eval (t : ℂ) - f t)
      (a.eval (u : ℂ) - deriv f u) u := by
    rw [← hpD]
    exact (p.hasDerivAt (u : ℂ)).comp_ofReal.sub ((hf.differentiable (by norm_num)) u).hasDerivAt
  have ha (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      ‖a.eval (u : ℂ) - deriv f u‖ ≤ ε := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t (_ : t ∈ Icc (0 : ℝ) 1) => (ha' t).hasDerivWithinAt)
      (fun t ht => (hq t (Ico_subset_Icc_self ht)).le) u hu
    simp only [Complex.ofReal_zero, ha0, sub_self, sub_zero] at h
    exact h.trans (mul_le_of_le_one_right hε.le (by linarith [hu.2]))
  refine ⟨p, fun u hu => ⟨?_, ?_, ?_⟩⟩
  · have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t (_ : t ∈ Icc (0 : ℝ) 1) => (hp' t).hasDerivWithinAt)
      (fun t ht => ha t (Ico_subset_Icc_self ht)) u hu
    simp only [Complex.ofReal_zero, hp0, sub_self, sub_zero] at h
    exact h.trans (mul_le_of_le_one_right hε.le (by linarith [hu.2]))
  · simpa only [hpD] using ha u hu
  · simpa only [hpD, haD] using (hq u hu).le

end
end ArtinMatthews
