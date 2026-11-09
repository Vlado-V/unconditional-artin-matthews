module

public import ArtinMatthews.VaryingKummerAnalyticRayPrimitiveIdealCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! Literal ideal-conductor Hecke series and right-half-plane holomorphy.
The coefficient is zero exactly at ideals not coprime to the actual ideal
conductor; no rational-modulus surrogate replaces that coprimality. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Set Filter
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M)

def coefficient (J : integralFractionalIdeals K) : ℂ :=
  if IsCoprime (EvenRayCharacter.underlyingIdeal J) M
  then (ψ.idealHom J.val : ℂ) else 0

theorem coefficient_norm_le_one (J : integralFractionalIdeals K) : ‖ψ.coefficient J‖ ≤ 1 := by
  unfold coefficient
  split_ifs
  · exact (ψ.idealHom_norm J.val).le
  · simp only [norm_zero,zero_le_one]

def dirichlet (s : ℂ) : ℂ :=
  ∑' J : integralFractionalIdeals K,
    ψ.coefficient J * ((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)^(-s)

theorem dirichlet_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : integralFractionalIdeals K =>
      ψ.coefficient J * ((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)^(-s)) := by
  apply Summable.of_norm_bounded (integralFractionalIdeals_norm_summable hs)
  intro J
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos J.val),Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (fractionalIdeal_absNorm_pos J.val).le _)
    (ψ.coefficient_norm_le_one J)

theorem dirichlet_differentiableOn :
    DifferentiableOn ℂ ψ.dirichlet {s : ℂ | 1 < s.re} := by
  intro s hs
  obtain ⟨t,ht,hts⟩ := exists_between (show 1 < s.re from hs)
  have h : DifferentiableOn ℂ ψ.dirichlet {z : ℂ | t < z.re} := by
    change DifferentiableOn ℂ (fun z : ℂ => ∑' J : integralFractionalIdeals K,
      ψ.coefficient J*((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)^(-z)) _
    apply Complex.differentiableOn_tsum_of_summable_norm (integralFractionalIdeals_norm_summable ht)
    · intro J
      exact ((differentiable_id.neg.const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos J.val).ne'))).const_mul
          (ψ.coefficient J)).differentiableOn
    · exact isOpen_lt continuous_const Complex.continuous_re
    · intro J z hz
      rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos J.val),Complex.neg_re]
      calc
        _ ≤ (FractionalIdeal.absNorm J.val.val : ℝ)^(-z.re) :=
          mul_le_of_le_one_left (Real.rpow_nonneg (fractionalIdeal_absNorm_pos J.val).le _)
            (ψ.coefficient_norm_le_one J)
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le
          (integralFractionalIdeals_absNorm_ge_one J) (neg_le_neg (le_of_lt hz))
  exact (h.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hts)).differentiableWithinAt

theorem dirichlet_analyticOnNhd : AnalyticOnNhd ℂ ψ.dirichlet {s : ℂ | 1 < s.re} :=
  ψ.dirichlet_differentiableOn.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/-- A uniform absolute majorant by the actual positive ideal norm series. -/
theorem dirichlet_norm_le_normSeries {s : ℂ} (hs : 1 < s.re) :
    ‖ψ.dirichlet s‖ ≤ ∑' J : integralFractionalIdeals K,
      (FractionalIdeal.absNorm J.val.val : ℝ)^(-s.re) := by
  have hsum := ψ.dirichlet_summable hs
  apply (norm_tsum_le_tsum_norm hsum.norm).trans
  apply hsum.norm.tsum_le_tsum _ (integralFractionalIdeals_norm_summable hs)
  intro J
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos J.val),Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (fractionalIdeal_absNorm_pos J.val).le _)
    (ψ.coefficient_norm_le_one J)


end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
