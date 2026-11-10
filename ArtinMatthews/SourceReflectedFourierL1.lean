module

public import ArtinMatthews.SourceReflectedAngularFourier


set_option backward.privateInPublic true
@[expose] public section

/-! The literal two-derivative bound for the Fourier L¹ cost. Compact
support converts suprema of the derivatives into their actual integrals. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Set
open scoped FourierTransform SchwartzMap BigOperators ContDiff
noncomputable section

private theorem sourceReflectedFourier_point (f : 𝓢(ℝ, ℂ)) {B : ℝ}
    (hderiv : ∀ i ≤ 2, (∫ x : ℝ, ‖iteratedFDeriv ℝ i f x‖) ≤ B)
    (k : ℕ) (hk : k ≤ 2) (ξ : ℝ) :
    ‖ξ‖ ^ k * ‖(𝓕 f) ξ‖ ≤ (2 : ℝ) ^ k * (k + 1) * B := by
  have hb := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (K := ⊤) (N := ⊤) (f := (f : ℝ → ℂ)) (f.smooth ⊤)
    (by intro a b ha hb; exact f.integrable_pow_mul_iteratedFDeriv volume a b)
    (k := 0) (n := k) (by simp) (by simp) ξ
  have hpt : ‖ξ‖ ^ k * ‖(𝓕 f) ξ‖ ≤
      (2 : ℝ) ^ k * ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
        ∫ x : ℝ, ‖x‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f x‖ := by
    simpa [SchwartzMap.fourier_coe] using hb
  apply hpt.trans
  calc
    _ ≤ (2 : ℝ) ^ k * ∑ _p ∈ Finset.range 1 ×ˢ Finset.range (k + 1), B := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hp
      have hp₁ : p.1 = 0 := by have h := Finset.mem_range.mp h₁; omega
      have hp₂ : p.2 ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp h₂)
      simpa only [hp₁, pow_zero, one_mul] using hderiv p.2 (hp₂.trans hk)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_product, Finset.card_range, one_mul,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

/-- The angular coefficient's L¹ norm is controlled by the actual
integrals of the function and its first two derivatives. -/
theorem sourceReflectedFourierCoefficient_L1_le (f : 𝓢(ℝ, ℂ)) {B : ℝ}
    (hderiv : ∀ i ≤ 2, (∫ x : ℝ, ‖iteratedFDeriv ℝ i f x‖) ≤ B) :
    (∫ τ : ℝ, ‖sourceReflectedFourierCoefficient f τ‖) ≤ 13 * Real.pi * B := by
  have hbound (ξ : ℝ) : ‖(𝓕 f) ξ‖ ≤ (13 * B) * (1 + ξ ^ 2)⁻¹ := by
    have h0 : ‖(𝓕 f) ξ‖ ≤ B := by
      simpa only [pow_zero, Nat.cast_zero, zero_add, one_mul] using
        sourceReflectedFourier_point f hderiv 0 (by decide) ξ
    have h2 : ξ ^ 2 * ‖(𝓕 f) ξ‖ ≤ 12 * B := by
      simpa only [Real.norm_eq_abs, sq_abs, Nat.cast_ofNat, show (2 : ℝ) ^ 2 * (2 + 1) = 12 by norm_num] using
        sourceReflectedFourier_point f hderiv 2 le_rfl ξ
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0 < 1 + ξ ^ 2)).mpr
    rw [mul_add, mul_one]
    nlinarith [h0, h2]
  rw [sourceReflectedFourierCoefficient_norm_integral]
  calc
    _ ≤ ∫ ξ : ℝ, (13 * B) * (1 + ξ ^ 2)⁻¹ :=
      integral_mono (𝓕 f).integrable.norm (integrable_inv_one_add_sq.const_mul _) hbound
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]; ring

/-- For a literal fixed support interval, the three derivative integrals
cost only its length. -/
theorem sourceReflectedFourierCoefficient_L1_of_compact (f : 𝓢(ℝ, ℂ)) {L B : ℝ}
    (hL : 0 ≤ L) (hsupp : tsupport f ⊆ Icc (-L) L)
    (hderiv : ∀ i ≤ 2, ∀ x ∈ Icc (-L) L, ‖iteratedFDeriv ℝ i f x‖ ≤ B) :
    (∫ τ : ℝ, ‖sourceReflectedFourierCoefficient f τ‖) ≤ 13 * Real.pi * ((2 * L) * B) := by
  apply sourceReflectedFourierCoefficient_L1_le f
  intro i hi
  have hsup : Function.support (iteratedFDeriv ℝ i (f : ℝ → ℂ)) ⊆ Icc (-L) L :=
    (support_iteratedFDeriv_subset i).trans hsupp
  have hfun : (fun x : ℝ => ‖iteratedFDeriv ℝ i f x‖) =
      (Icc (-L) L).indicator (fun x : ℝ => ‖iteratedFDeriv ℝ i f x‖) := by
    funext x
    by_cases hx : x ∈ Icc (-L) L
    · rw [indicator_of_mem hx]
    · have hz : iteratedFDeriv ℝ i f x = 0 :=
        Function.notMem_support.mp (fun hs => hx (hsup hs))
      rw [indicator_of_notMem hx, hz, norm_zero]
  conv_lhs => rw [hfun, integral_indicator measurableSet_Icc]
  calc
    _ ≤ ∫ x in Icc (-L) L, B := by
      have hI := f.integrable_pow_mul_iteratedFDeriv volume 0 i
      simp only [pow_zero, one_mul] at hI
      exact setIntegral_mono_on hI.integrableOn (integrableOn_const isCompact_Icc.measure_lt_top.ne)
        measurableSet_Icc (hderiv i hi)
    _ = _ := by
      rw [setIntegral_const, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
      ring

end
end ArtinMatthews.SourceReflection
