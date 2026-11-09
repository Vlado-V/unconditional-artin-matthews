module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleFrequencyLabels


set_option backward.privateInPublic true
@[expose] public section

/-! Sharp arithmetic spacing for primitive trace frequencies on a fixed
ideal I: the denominator contains a single factor Norm(I). -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem idealModule_traceDual_contains_difference
    (I M N : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥) (hN : N ≠ ⊥) {a b r : K}
    (ha : a ∈ FractionalIdeal.dual ℤ ℚ ((M * I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
    (hb : b ∈ FractionalIdeal.dual ℤ ℚ ((N * I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
    (hr : r ∈ FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    a - b + r ∈ FractionalIdeal.dual ℤ ℚ
      ((M * N * I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  have hP : M * N * I ≠ ⊥ := mul_ne_zero (mul_ne_zero hM hN) hI
  have hMI : M * N * I ≤ M * I := by
    simpa only [mul_assoc, mul_comm N I] using
      (Ideal.mul_le_left : (M * I) * N ≤ M * I)
  have hNI : M * N * I ≤ N * I := by
    simpa only [mul_comm M N, mul_assoc, mul_comm M I] using
      (Ideal.mul_le_left : (N * I) * M ≤ N * I)
  have hPI : M * N * I ≤ I := Ideal.mul_le_right
  have hm := (FractionalIdeal.dual_le_dual ℤ ℚ
    (FractionalIdeal.coeIdeal_ne_zero.mpr (mul_ne_zero hM hI))
    (FractionalIdeal.coeIdeal_ne_zero.mpr hP)).mpr
      ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr hMI) ha
  have hn := (FractionalIdeal.dual_le_dual ℤ ℚ
    (FractionalIdeal.coeIdeal_ne_zero.mpr (mul_ne_zero hN hI))
    (FractionalIdeal.coeIdeal_ne_zero.mpr hP)).mpr
      ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr hNI) hb
  have hi := (FractionalIdeal.dual_le_dual ℤ ℚ
    (FractionalIdeal.coeIdeal_ne_zero.mpr hI)
    (FractionalIdeal.coeIdeal_ne_zero.mpr hP)).mpr
      ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr hPI) hr
  exact (FractionalIdeal.dual ℤ ℚ
    ((M * N * I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).val.add_mem
    ((FractionalIdeal.dual ℤ ℚ
      ((M * N * I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)).val.sub_mem hm hn) hi

theorem idealModuleFrequency_mixed_separation
    (I M N : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥) (hN : N ≠ ⊥) {a b r : K}
    (ha : a ∈ FractionalIdeal.dual ℤ ℚ ((M * I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
    (hb : b ∈ FractionalIdeal.dual ℤ ℚ ((N * I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
    (hr : r ∈ FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (hne : a - b + r ≠ 0) :
    1 / (|(NumberField.discr K : ℝ)| * (Ideal.absNorm M : ℝ) *
      (Ideal.absNorm N : ℝ) * (Ideal.absNorm I : ℝ)) ≤
      ‖mixedEmbedding K (a - b + r)‖ ^ Module.finrank ℚ K := by
  have h := traceDual_element_mixed_norm_pow_lower K (M * N * I)
    (mul_ne_zero (mul_ne_zero hM hN) hI) hne
    (idealModule_traceDual_contains_difference K I M N hI hM hN ha hb hr)
  simpa only [map_mul, Nat.cast_mul, mul_assoc] using h

theorem idealModuleFrequencyLabel_mixed_separation
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) {ℓ ℓ' : IdealFrequencyLabel K} (hne : ℓ ≠ ℓ') {r : K}
    (hr : r ∈ FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    1 / (|(NumberField.discr K : ℝ)| * (Ideal.absNorm ℓ.1.val : ℝ) *
      (Ideal.absNorm ℓ'.1.val : ℝ) * (Ideal.absNorm I : ℝ)) ≤
      ‖mixedEmbedding K
        (idealModuleFrequencyLabelValue K I hI ℓ - idealModuleFrequencyLabelValue K I hI ℓ' + r)‖ ^
        Module.finrank ℚ K :=
  idealModuleFrequency_mixed_separation K I ℓ.1.val ℓ'.1.val hI ℓ.1.property ℓ'.1.property
    (idealModuleFrequencyValue_mem_dual K I ℓ.1.val hI ℓ.1.property ℓ.2)
    (idealModuleFrequencyValue_mem_dual K I ℓ'.1.val hI ℓ'.1.property ℓ'.2) hr
    (idealModuleFrequencyLabel_difference_ne_zero K I hI hne hr)

theorem idealModuleFrequencyLabel_mixed_separation_norm_cutoff
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) {ℓ ℓ' : IdealFrequencyLabel K} (hne : ℓ ≠ ℓ') {r : K}
    (hr : r ∈ FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) {U : ℝ}
    (hℓU : (Ideal.absNorm ℓ.1.val : ℝ) ≤ U)
    (hℓ'U : (Ideal.absNorm ℓ'.1.val : ℝ) ≤ U) :
    1 / (|(NumberField.discr K : ℝ)| * (Ideal.absNorm I : ℝ) * U ^ 2) ≤
      ‖mixedEmbedding K
        (idealModuleFrequencyLabelValue K I hI ℓ - idealModuleFrequencyLabelValue K I hI ℓ' + r)‖ ^
        Module.finrank ℚ K := by
  have hD : 0 < |(NumberField.discr K : ℝ)| := abs_pos.mpr (by
    exact_mod_cast NumberField.discr_ne_zero K)
  have hIN : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero ((Ideal.absNorm_eq_zero_iff).not.mpr hI)
  have hm : 0 < (Ideal.absNorm ℓ.1.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero ((Ideal.absNorm_eq_zero_iff).not.mpr ℓ.1.property)
  have hn : 0 < (Ideal.absNorm ℓ'.1.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero ((Ideal.absNorm_eq_zero_iff).not.mpr ℓ'.1.property)
  have hU : 0 ≤ U := hm.le.trans hℓU
  apply (one_div_le_one_div_of_le (mul_pos (mul_pos (mul_pos hD hm) hn) hIN) ?_).trans
    (idealModuleFrequencyLabel_mixed_separation K I hI hne hr)
  have H := mul_le_mul hℓU hℓ'U hn.le hU
  have H' := mul_le_mul_of_nonneg_left H (mul_pos hD hIN).le
  nlinarith

end
end ArtinMatthews.VaryingKummerAnalytic
