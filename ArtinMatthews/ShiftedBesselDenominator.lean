module

public import ArtinMatthews.ShiftedBesselScale


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform smoothness in the circle denominator. The inverse-square dual
argument multiplies its j-th logarithmic derivative by (-2)^j. The genuine
source-seminorm Bessel estimate therefore controls denominator derivatives
without introducing a scale-dependent smoothness assumption. -/

noncomputable section
open Complex Real Set OAI
open scoped ContDiff

namespace ArtinMatthews

private theorem euler_inverse_square (G : ℝ → ℂ) (x q : ℝ) (hq : 0 < q) (j : ℕ)
    (hG : ContDiff ℝ ∞ (fun t : ℝ ↦ G ((x/q^2)*Real.exp t))) :
    LocalLogFourier.eulerDeriv (fun z ↦ G (x/z^2)) j q =
      ((-2 : ℝ)^j) • LocalLogFourier.eulerDeriv G j (x/q^2) := by
  have he (t : ℝ) : x/(q*Real.exp t)^2 = (x/q^2)*Real.exp ((-2)*t) := by
    rw [show (-2 : ℝ)*t = -(t+t) by ring, Real.exp_neg, Real.exp_add, mul_pow]
    field_simp
  have hf : (fun t : ℝ ↦ G (x/(q*Real.exp t)^2)) =
      (fun t : ℝ ↦ (fun s : ℝ ↦ G ((x/q^2)*Real.exp s)) ((-2 : ℝ) • t)) := by
    funext t
    simp only [smul_eq_mul, he]
  unfold LocalLogFourier.eulerDeriv
  rw [hf]
  have hh := congrArg (fun g : ℝ → ℂ ↦ g 0)
    (iteratedDeriv_comp_const_smul (n := j) (hG.of_le (by simp)) (-2 : ℝ))
  simpa only [smul_eq_mul, mul_zero] using hh

/-- The scaled kernel remains smooth along every positive logarithmic ray. -/
theorem weightOneBesselTransform_dilate_log_smooth (W : SchwartzMap ℝ ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hWs : Function.support W ⊆ Icc 0 B)
    (K y : ℝ) (hK : 0 < K) (hy : 0 < y) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ weightOneBesselTransform (fun x ↦ W (x/K)) (y*Real.exp t)) := by
  have hs := weightOneBesselTransform_log_smooth W B hB hWs (K*y) (mul_pos hK hy)
  have ht : ContDiff ℝ ∞ (fun t : ℝ ↦ (K : ℂ)*weightOneBesselTransform W ((K*y)*Real.exp t)) :=
    contDiff_const.mul hs
  convert ht using 1
  funext t
  rw [weightOneBesselTransform_dilate W K _ hK]
  congr 1
  congr 1
  ring

/-- Exact denominator derivative formula at the actual argument x/q². -/
theorem weightOneBesselTransform_denominator_euler (W : SchwartzMap ℝ ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hWs : Function.support W ⊆ Icc 0 B)
    (K x q : ℝ) (hK : 0 < K) (hx : 0 < x) (hq : 0 < q) (j : ℕ) :
    LocalLogFourier.eulerDeriv
      (fun z ↦ weightOneBesselTransform (fun t ↦ W (t/K)) (x/z^2)) j q =
        ((-2 : ℝ)^j) • ((K : ℂ) *
          LocalLogFourier.eulerDeriv (weightOneBesselTransform W) j (K*(x/q^2))) := by
  have hy : 0 < x/q^2 := div_pos hx (sq_pos_of_pos hq)
  rw [euler_inverse_square _ x q hq j
    (weightOneBesselTransform_dilate_log_smooth W B hB hWs K _ hK hy),
    weightOneBesselTransform_dilate_euler W B hB hWs K _ hK hy j]

/-- The circle-denominator derivatives have the same dual-length decay and
source-seminorm control, with the explicit harmless factor 2^j. -/
theorem weightOneBesselTransform_denominator_source_bound (A J : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (B : ℝ), 0 ≤ B → Function.support W ⊆ Icc 0 B →
        ∀ (K x q : ℝ), 0 < K → 0 < x → 0 < q → ∀ (j : ℕ), j ≤ J →
          (1+K*(x/q^2))^A * ‖LocalLogFourier.eulerDeriv
            (fun z ↦ weightOneBesselTransform (fun t ↦ W (t/K)) (x/z^2)) j q‖ ≤
              2^j*C*K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s,C,hC,hb⟩ := weightOneBesselTransform_euler_source_bound A J
  refine ⟨s,C,hC,?_⟩
  intro W B hB hWs K x q hK hx hq j hj
  rw [weightOneBesselTransform_denominator_euler W B hB hWs K x q hK hx hq j,
    norm_smul, Real.norm_eq_abs, abs_pow, abs_neg, abs_of_pos (by norm_num : (0 : ℝ)<2),
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK]
  have hh := mul_le_mul_of_nonneg_left
    (hb W B hB hWs j hj (K*(x/q^2)) (mul_pos hK (div_pos hx (sq_pos_of_pos hq))))
    (show 0 ≤ (2 : ℝ)^j*K by positivity)
  nlinarith

end ArtinMatthews
