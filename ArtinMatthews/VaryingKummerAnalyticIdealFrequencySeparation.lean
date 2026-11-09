module

public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualNormIdeal
public import ArtinMatthews.VaryingKummerAnalyticDedekindSeriesPartialComplex


set_option backward.privateInPublic true
@[expose] public section

/-! Arithmetic spacing of ideal-quotient frequencies in the actual mixed
embedding. The discriminant and both modulus norms are retained explicitly. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem fractionalIdeal_absNorm_le_element_norm
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {a : K} (ha : a ≠ 0) (haI : a ∈ I.val) :
    (FractionalIdeal.absNorm I.val : ℝ) ≤ |(Algebra.norm ℚ a : ℝ)| := by
  let α : Kˣ := Units.mk0 a ha
  let J := relativeElementIdeal I α
  have hJ : J.val ≤ 1 := (relativeElementIdeal_le_one_iff I α).mpr haI
  have hN := integralFractionalIdeals_absNorm_ge_one ⟨J,hJ⟩
  have hm : J * I = toPrincipalIdeal (𝓞 K) K α := by simp [J,relativeElementIdeal]
  have hn := congrArg (fun U : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
    (FractionalIdeal.absNorm U.val : ℝ)) hm
  simp only [Units.val_mul,map_mul,coe_toPrincipalIdeal,FractionalIdeal.absNorm_span_singleton,
    Rat.cast_mul,Rat.cast_abs,Units.val_mk0,α] at hn
  calc
    (FractionalIdeal.absNorm I.val : ℝ) = 1 * (FractionalIdeal.absNorm I.val : ℝ) := by ring
    _ ≤ (FractionalIdeal.absNorm J.val : ℝ) * (FractionalIdeal.absNorm I.val : ℝ) :=
      mul_le_mul_of_nonneg_right hN (fractionalIdeal_absNorm_pos I).le
    _ = _ := hn

theorem algebraNorm_le_mixedEmbedding_norm_pow (a : K) :
    |(Algebra.norm ℚ a : ℝ)| ≤ ‖mixedEmbedding K a‖ ^ Module.finrank ℚ K := by
  rw [← Rat.cast_abs, ← mixedEmbedding.norm_eq_norm, mixedEmbedding.norm_apply]
  calc
    (∏ w, mixedEmbedding.normAtPlace w (mixedEmbedding K a) ^ w.mult) ≤
        ∏ w : InfinitePlace K, ‖mixedEmbedding K a‖ ^ w.mult := by
      apply Finset.prod_le_prod₀
      · intro w _
        exact pow_nonneg (mixedEmbedding.normAtPlace_nonneg _ _) _
      · intro w _
        apply pow_le_pow_left₀ (mixedEmbedding.normAtPlace_nonneg _ _)
        rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
        exact Finset.le_sup' (fun v : InfinitePlace K =>
          mixedEmbedding.normAtPlace v (mixedEmbedding K a)) (Finset.mem_univ w)
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

theorem traceDual_element_mixed_norm_pow_lower
    (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) {a : K} (ha : a ≠ 0)
    (haM : a ∈ FractionalIdeal.dual ℤ ℚ (M : FractionalIdeal (𝓞 K)⁰ K)) :
    1 / (|(NumberField.discr K : ℝ)| * (Ideal.absNorm M : ℝ)) ≤
      ‖mixedEmbedding K a‖ ^ Module.finrank ℚ K := by
  let I : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    Units.mk0 (M : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr hM)
  have h := fractionalIdeal_absNorm_le_element_norm K (mixedTraceDualIdeal K I) ha haM
  rw [mixedTraceDualIdeal_absNorm_div] at h
  simp only [I,Units.val_mk0,FractionalIdeal.coeIdeal_absNorm,
    Rat.cast_natCast] at h
  exact h.trans (algebraNorm_le_mixedEmbedding_norm_pow K a)

theorem traceDual_product_element_mixed_norm_pow_lower
    (M N : Ideal (𝓞 K)) (hM : M ≠ ⊥) (hN : N ≠ ⊥) {a : K} (ha : a ≠ 0)
    (haMN : a ∈ FractionalIdeal.dual ℤ ℚ ((M*N : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) :
    1 / (|(NumberField.discr K : ℝ)| * (Ideal.absNorm M : ℝ) * (Ideal.absNorm N : ℝ)) ≤
      ‖mixedEmbedding K a‖ ^ Module.finrank ℚ K := by
  have hMN : M*N ≠ ⊥ := mul_ne_zero hM hN
  have h := traceDual_element_mixed_norm_pow_lower K (M*N) hMN ha haMN
  simpa only [map_mul,Nat.cast_mul,mul_assoc] using h

theorem traceDual_product_contains_difference
    (M N : Ideal (𝓞 K)) (hM : M ≠ ⊥) (hN : N ≠ ⊥) {a b r : K}
    (ha : a ∈ FractionalIdeal.dual ℤ ℚ (M : FractionalIdeal (𝓞 K)⁰ K))
    (hb : b ∈ FractionalIdeal.dual ℤ ℚ (N : FractionalIdeal (𝓞 K)⁰ K))
    (hr : r ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    a-b+r ∈ FractionalIdeal.dual ℤ ℚ ((M*N : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  have hMN : M*N ≠ ⊥ := mul_ne_zero hM hN
  have hm : ((M*N : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≤ M :=
    (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr Ideal.mul_le_left
  have hn : ((M*N : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≤ N :=
    (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr Ideal.mul_le_right
  have h1 : ((M*N : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 :=
    FractionalIdeal.coeIdeal_le_one
  have ham := (FractionalIdeal.dual_le_dual ℤ ℚ
    (FractionalIdeal.coeIdeal_ne_zero.mpr hM) (FractionalIdeal.coeIdeal_ne_zero.mpr hMN)).mpr hm ha
  have hbn := (FractionalIdeal.dual_le_dual ℤ ℚ
    (FractionalIdeal.coeIdeal_ne_zero.mpr hN) (FractionalIdeal.coeIdeal_ne_zero.mpr hMN)).mpr hn hb
  have hr1 := (FractionalIdeal.dual_le_dual ℤ ℚ
    one_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hMN)).mpr h1 hr
  exact (FractionalIdeal.dual ℤ ℚ ((M*N : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).val.add_mem
    ((FractionalIdeal.dual ℤ ℚ ((M*N : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).val.sub_mem ham hbn) hr1

theorem idealFrequency_mixed_separation
    (M N : Ideal (𝓞 K)) (hM : M ≠ ⊥) (hN : N ≠ ⊥) {a b r : K}
    (ha : a ∈ FractionalIdeal.dual ℤ ℚ (M : FractionalIdeal (𝓞 K)⁰ K))
    (hb : b ∈ FractionalIdeal.dual ℤ ℚ (N : FractionalIdeal (𝓞 K)⁰ K))
    (hr : r ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))
    (hne : a-b+r ≠ 0) :
    1 / (|(NumberField.discr K : ℝ)| * (Ideal.absNorm M : ℝ) * (Ideal.absNorm N : ℝ)) ≤
      ‖mixedEmbedding K (a-b+r)‖ ^ Module.finrank ℚ K :=
  traceDual_product_element_mixed_norm_pow_lower K M N hM hN hne
    (traceDual_product_contains_difference K M N hM hN ha hb hr)


theorem idealFrequency_mixed_separation_norm_cutoff
    (M N : Ideal (𝓞 K)) (hM : M ≠ ⊥) (hN : N ≠ ⊥) {a b r : K}
    (ha : a ∈ FractionalIdeal.dual ℤ ℚ (M : FractionalIdeal (𝓞 K)⁰ K))
    (hb : b ∈ FractionalIdeal.dual ℤ ℚ (N : FractionalIdeal (𝓞 K)⁰ K))
    (hr : r ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))
    (hne : a-b+r ≠ 0) {U : ℝ}
    (hMU : (Ideal.absNorm M : ℝ) ≤ U) (hNU : (Ideal.absNorm N : ℝ) ≤ U) :
    1 / (|(NumberField.discr K : ℝ)| * U^2) ≤
      ‖mixedEmbedding K (a-b+r)‖ ^ Module.finrank ℚ K := by
  have hD : 0 < |(NumberField.discr K : ℝ)| := abs_pos.mpr (by
    exact_mod_cast NumberField.discr_ne_zero K)
  have hm : 0 < (Ideal.absNorm M : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero ((Ideal.absNorm_eq_zero_iff).not.mpr hM)
  have hn : 0 < (Ideal.absNorm N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero ((Ideal.absNorm_eq_zero_iff).not.mpr hN)
  have hU : 0 ≤ U := hm.le.trans hMU
  apply (one_div_le_one_div_of_le (mul_pos (mul_pos hD hm) hn) ?_).trans
    (idealFrequency_mixed_separation K M N hM hN ha hb hr hne)
  have H := mul_le_mul hMU hNU hn.le hU
  nlinarith

end
end ArtinMatthews.VaryingKummerAnalytic
