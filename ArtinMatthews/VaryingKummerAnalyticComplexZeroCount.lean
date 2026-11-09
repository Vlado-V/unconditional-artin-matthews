module

public import ArtinMatthews.VaryingKummerAnalyticComplexZeroPole


set_option backward.privateInPublic true
@[expose] public section

/-! Local zero multiplicity bounds from the actual nonnegative pole sum. -/
namespace OAI.PrimeDegreePackets.AnalyticGrowth

open ArtinMatthews.ReusedGrowth
open Complex
open scoped BigOperators

lemma one_le_five_mul_inverse_re {ρ : ℂ} {T : ℝ}
    (hρ₀ : 0 ≤ ρ.re) (hρ₁ : ρ.re ≤ 1) (hT : |T-ρ.im| ≤ 1) :
    1 ≤ 5 * (1 / ((⟨2,T⟩ : ℂ) - ρ)).re := by
  have hb := abs_le.mp hT
  have hq : 0 ≤ ρ.re * (1-ρ.re) := mul_nonneg hρ₀ (by linarith)
  have ht : 0 ≤ (1-(T-ρ.im))*(1+(T-ρ.im)) :=
    mul_nonneg (by linarith) (by linarith)
  have hd : 0 < (2-ρ.re)*(2-ρ.re)+(T-ρ.im)*(T-ρ.im) := by
    nlinarith [sq_nonneg (T-ρ.im)]
  simp only [one_div, Complex.inv_re, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im]
  change 1 ≤ 5*((2-ρ.re)/((2-ρ.re)*(2-ρ.re)+(T-ρ.im)*(T-ρ.im)))
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hd).2
  nlinarith

theorem finite_zero_height_window_bound {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hg : HasSubquadraticGrowth f) (hfe : ∀ z, f (1-z) = f z)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    (S : Finset ℂ) (T : ℝ) (hT : ∀ ρ ∈ S, |T-ρ.im| ≤ 1) :
    (∑ ρ ∈ S, (zeroMultiplicity f ρ : ℝ)) ≤
      5*(logDeriv f (⟨2,T⟩ : ℂ)).re := by
  classical
  have hs : 1 < (⟨2,T⟩ : ℂ).re := by norm_num
  have H := hasSum_complexZeroPole hf h0 hg hfe hstrip hs
  have HN := complexZeroPole_nonneg hf h0 hstrip hs
  have HP (ρ : ℂ) (hρ : ρ ∈ S) :
      (zeroMultiplicity f ρ : ℝ) ≤ 5*complexZeroPole f (⟨2,T⟩ : ℂ) ρ := by
    by_cases hm : zeroMultiplicity f ρ = 0
    · simp [complexZeroPole,hm]
    have hz := (zeroMultiplicity_ne_zero_iff hf h0 ρ).mp hm
    have hr := hstrip ρ hz
    have hl := hstrip (1-ρ) (by rwa [hfe])
    have hρ₀ : 0 ≤ ρ.re := by
      simp only [Complex.sub_re,Complex.one_re] at hl
      linarith
    have hi := one_le_five_mul_inverse_re hρ₀ hr (hT ρ hρ)
    have hm₀ : (0 : ℝ) ≤ zeroMultiplicity f ρ := by
      exact_mod_cast zeroMultiplicity_nonneg hf ρ
    have hmul := mul_le_mul_of_nonneg_left hi hm₀
    unfold complexZeroPole
    nlinarith
  calc
    _ ≤ ∑ ρ ∈ S, 5*complexZeroPole f (⟨2,T⟩ : ℂ) ρ := Finset.sum_le_sum HP
    _ = 5 * ∑ ρ ∈ S, complexZeroPole f (⟨2,T⟩ : ℂ) ρ := by rw [Finset.mul_sum]
    _ ≤ 5 * ∑' ρ, complexZeroPole f (⟨2,T⟩ : ℂ) ρ :=
      mul_le_mul_of_nonneg_left (H.summable.sum_le_tsum S (fun ρ _ => HN ρ)) (by norm_num)
    _ = _ := by rw [H.tsum_eq]

end OAI.PrimeDegreePackets.AnalyticGrowth
