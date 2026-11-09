module

public import ArtinMatthews.SpectralBesselJOrderJoint
public import ArtinMatthews.SpectralBesselJAllX
public import Mathlib.Analysis.Complex.Liouville


set_option backward.privateInPublic true
@[expose] public section

/-! A uniform complex-order derivative bound at bounded positive arguments.
Factoring off the exact power isolates the small-argument logarithm. -/
namespace ArtinMatthews
open Complex Set
noncomputable section

private def spectralJFactoredOrder (x : ℝ) (ν : ℂ) : ℂ :=
  (x : ℂ)^(-ν) * Complex.besselJ ν (x : ℂ)

private theorem spectral_besselJ_eq_factoredOrder {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    (x : ℂ)^ν * spectralJFactoredOrder x ν = Complex.besselJ ν (x : ℂ) := by
  rw [spectralJFactoredOrder, ← mul_assoc,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'),
    add_neg_cancel, Complex.cpow_zero, one_mul]

private theorem spectralJFactoredOrder_differentiable {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (spectralJFactoredOrder x) := by
  intro ν
  have hp : DifferentiableAt ℂ (fun w : ℂ => (x : ℂ)^(-w)) ν :=
    (((hasDerivAt_id ν).neg).const_cpow (c := (x : ℂ))
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).differentiableAt
  exact hp.mul (spectral_besselJ_order_differentiable hx ν)

private theorem spectral_invGamma_compact_six_bound :
    ∃ G : ℝ, 0 < G ∧ ∀ z : ℂ, ‖z‖ ≤ 6 → ‖(Complex.Gamma z)⁻¹‖ ≤ G := by
  have hΓ : Continuous (fun z : ℂ => ‖(Complex.Gamma z)⁻¹‖) :=
    Complex.differentiable_one_div_Gamma.continuous.norm
  obtain ⟨G,hG⟩ := ((isCompact_closedBall (0 : ℂ) 6).image hΓ).bddAbove
  refine ⟨max 1 G, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro z hz
  exact (hG ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, rfl⟩).trans
    (le_max_right _ _)

private theorem spectral_besselJ_shifted_order_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ (ν : ℂ) (x a : ℝ), 0 < x → ‖ν‖ ≤ 3 →
      -(3/4 : ℝ) ≤ ν.re → 1 ≤ a → a ≤ 2 →
      ‖Complex.besselJ (ν+(a : ℂ)) (x : ℂ)‖ ≤ A*x^(ν.re+a) := by
  obtain ⟨C,hC,hJ⟩ := spectral_besselJ_poisson_norm_gamma_inv
  obtain ⟨G,hG,hΓ⟩ := spectral_invGamma_compact_six_bound
  refine ⟨C*G, mul_pos hC hG, ?_⟩
  intro ν x a hx hν hr ha ha₂
  have harg : ‖ν+(a : ℂ)+1/2‖ ≤ 6 := by
    calc
      _ ≤ ‖ν‖+‖(a : ℂ)‖+‖(1/2 : ℂ)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ a)]
        norm_num
        linarith
  have hνa : (ν+(a : ℂ)).re = ν.re+a := by simp
  have hp : 0 ≤ (ν+(a : ℂ)).re := by rw [hνa]; linarith
  calc
    _ ≤ C*x^(ν.re+a)*‖(Complex.Gamma (ν+(a : ℂ)+1/2))⁻¹‖ := by
      simpa only [hνa] using hJ (ν+(a : ℂ)) x hp hx
    _ ≤ C*x^(ν.re+a)*G :=
      mul_le_mul_of_nonneg_left (hΓ _ harg) (by positivity)
    _ = _ := by ring

private theorem spectralJFactoredOrder_bound (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (ν : ℂ), 0 < x → x ≤ B → ‖ν‖ ≤ 3 →
      -(3/4 : ℝ) ≤ ν.re → ‖spectralJFactoredOrder x ν‖ ≤ C := by
  obtain ⟨A,hA,hJ⟩ := spectral_besselJ_shifted_order_bound
  refine ⟨A*(8+B^2), by positivity, ?_⟩
  intro x ν hx hxB hn hr
  have h₁ : ‖Complex.besselJ (ν+1) (x : ℂ)‖ ≤ A*x^(ν.re+1) := by
    simpa only [Complex.ofReal_one] using hJ ν x 1 hx hn hr (by norm_num) (by norm_num)
  have h₂ : ‖Complex.besselJ (ν+2) (x : ℂ)‖ ≤ A*x^(ν.re+2) := by
    simpa only [Complex.ofReal_ofNat] using hJ ν x 2 hx hn hr (by norm_num) (by norm_num)
  have hJν : ‖Complex.besselJ ν (x : ℂ)‖ ≤
      (2*‖ν+1‖/x)*(A*x^(ν.re+1)) + A*x^(ν.re+2) := by
    rw [spectral_besselJ_order_recurrence ν hx]
    calc
      _ ≤ ‖2*(ν+1)/(x : ℂ)*Complex.besselJ (ν+1) (x : ℂ)‖ +
          ‖Complex.besselJ (ν+2) (x : ℂ)‖ := norm_sub_le _ _
      _ = (2*‖ν+1‖/x)*‖Complex.besselJ (ν+1) (x : ℂ)‖ +
          ‖Complex.besselJ (ν+2) (x : ℂ)‖ := by
        rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.le]
        norm_num
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h₁ (by positivity)) h₂
  have hν₁ : ‖ν+1‖ ≤ 4 := by
    calc
      _ ≤ ‖ν‖+‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_one]; linarith
  have hpow₁ : x^(ν.re+1) = x^ν.re*x := by rw [Real.rpow_add hx, Real.rpow_one]
  have hpow₂ : x^(ν.re+2) = x^ν.re*x^2 := by
    rw [Real.rpow_add hx]
    norm_cast
  have hcancel : x^(-ν.re)*x^ν.re = 1 := by rw [← Real.rpow_add hx, neg_add_cancel, Real.rpow_zero]
  rw [spectralJFactoredOrder, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]
  calc
    _ ≤ x^(-ν.re)*((2*‖ν+1‖/x)*(A*x^(ν.re+1)) + A*x^(ν.re+2)) :=
      mul_le_mul_of_nonneg_left hJν (Real.rpow_nonneg hx.le _)
    _ = (x^(-ν.re)*x^ν.re)*(A*(2*‖ν+1‖+x^2)) := by
      rw [hpow₁,hpow₂]
      field_simp [hx.ne'] <;> ring
    _ = A*(2*‖ν+1‖+x^2) := by rw [hcancel,one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by linarith [pow_le_pow_left₀ hx.le hxB 2]) hA.le

theorem spectral_besselJ_order_deriv_norm_le_bounded (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (ν : ℂ), 0 < x → x ≤ B → ‖ν‖ ≤ 2 →
      -(1/2 : ℝ) ≤ ν.re →
      ‖deriv (fun w : ℂ => Complex.besselJ w (x : ℂ)) ν‖ ≤
        C*x^ν.re*(1+|Real.log x|) := by
  obtain ⟨C,hC,hcore⟩ := spectralJFactoredOrder_bound B
  refine ⟨4*C, by positivity, ?_⟩
  intro x ν hx hxB hn hr
  have hd : Differentiable ℂ (spectralJFactoredOrder x) :=
    spectralJFactoredOrder_differentiable hx
  have hder : ‖deriv (spectralJFactoredOrder x) ν‖ ≤ 4*C := by
    have hs := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (c := ν) (R := 1/4) (C := C) (f := spectralJFactoredOrder x)
      (by norm_num) hd.diffContOnCl (by
        intro w hw
        rw [Metric.mem_sphere, dist_eq_norm] at hw
        apply hcore x w hx hxB
        · calc
            ‖w‖ = ‖(w-ν)+ν‖ := by rw [sub_add_cancel]
            _ ≤ ‖w-ν‖+‖ν‖ := norm_add_le _ _
            _ ≤ 3 := by linarith
        · have h := Complex.abs_re_le_norm (w-ν)
          rw [Complex.sub_re,hw] at h
          linarith [(abs_le.mp h).1])
    convert hs using 1 <;> ring
  have hp : HasDerivAt (fun w : ℂ => (x : ℂ)^w)
      ((x : ℂ)^ν*Complex.log (x : ℂ)) ν := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id ν).const_cpow (c := (x : ℂ))
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have he : (fun w : ℂ => (x : ℂ)^w*spectralJFactoredOrder x w) =
      fun w => Complex.besselJ w (x : ℂ) := funext (spectral_besselJ_eq_factoredOrder hx)
  have hj := hp.mul (hd ν).hasDerivAt
  change HasDerivAt (fun w : ℂ => (x : ℂ)^w*spectralJFactoredOrder x w) _ ν at hj
  rw [he] at hj
  rw [hj.deriv]
  have hCν : ‖spectralJFactoredOrder x ν‖ ≤ C :=
    hcore x ν hx hxB (hn.trans (by norm_num)) (by linarith)
  have hadd : |Real.log x| * ‖spectralJFactoredOrder x ν‖ +
      ‖deriv (spectralJFactoredOrder x) ν‖ ≤ (4*C)*(1+|Real.log x|) := by
    calc
      _ ≤ |Real.log x| * C+4*C :=
        add_le_add (mul_le_mul_of_nonneg_left hCν (abs_nonneg _)) hder
      _ ≤ _ := by nlinarith [mul_nonneg (abs_nonneg (Real.log x)) hC.le]
  calc
    _ ≤ ‖((x : ℂ)^ν*Complex.log (x : ℂ))*spectralJFactoredOrder x ν‖ +
        ‖(x : ℂ)^ν*deriv (spectralJFactoredOrder x) ν‖ := norm_add_le _ _
    _ = x^ν.re*(|Real.log x| * ‖spectralJFactoredOrder x ν‖ +
        ‖deriv (spectralJFactoredOrder x) ν‖) := by
      simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, ← Complex.ofReal_log hx.le,
        Complex.norm_real, Real.norm_eq_abs]
      ring
    _ ≤ x^ν.re*((4*C)*(1+|Real.log x|)) :=
      mul_le_mul_of_nonneg_left hadd (Real.rpow_nonneg hx.le _)
    _ = _ := by ring

end
end ArtinMatthews
