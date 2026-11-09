module

public import ArtinMatthews.VaryingKummerAnalyticRayClassSeries
public import ArtinMatthews.VaryingKummerAnalyticDedekindSeriesClasses


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine ideal-class-weighted Dirichlet series in arbitrary signature.
Only generic convergence/partition proofs are extracted from NormalClosure. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField FractionalIdeal Set Module Filter Topology
open scoped NumberField nonZeroDivisors Classical BigOperators

def idealClassDirichlet (K : Type*) [Field K] [NumberField K]
    (w : ClassGroup (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∑' J : integralFractionalIdeals K,
    w (ClassGroup.mk K J.1) * ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ)^(-s)

lemma idealClassDirichlet_summable {K : Type*} [Field K] [NumberField K]
    (w : ClassGroup (𝓞 K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : integralFractionalIdeals K =>
      w (ClassGroup.mk K J.1) * ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ)^(-s)) := by
  classical
  let M := ∑ c : ClassGroup (𝓞 K), ‖w c‖
  apply Summable.of_norm_bounded ((integralFractionalIdeals_norm_summable hs).mul_left M)
  intro J
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos _), Complex.neg_re]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)
  exact Finset.single_le_sum (fun c _ => norm_nonneg (w c)) (Finset.mem_univ _)

lemma idealClassDirichlet_differentiableOn {K : Type*} [Field K] [NumberField K]
    (w : ClassGroup (𝓞 K) → ℂ) :
    DifferentiableOn ℂ (idealClassDirichlet K w) {s | 1 < s.re} := by
  classical
  intro s hs
  obtain ⟨t,ht,hts⟩ := exists_between (show 1 < s.re from hs)
  let M := ∑ c : ClassGroup (𝓞 K), ‖w c‖
  have H : DifferentiableOn ℂ (idealClassDirichlet K w) {z | t < z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      ((integralFractionalIdeals_norm_summable ht).mul_left M)
    · intro J
      apply Differentiable.differentiableOn
      apply Differentiable.const_mul
      apply Differentiable.const_cpow (differentiable_id.neg)
      exact Or.inl (Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos _).ne')
    · exact isOpen_lt continuous_const Complex.continuous_re
    · intro J z hz
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos _), Complex.neg_re]
      apply mul_le_mul
      · exact Finset.single_le_sum (fun c _ => norm_nonneg (w c)) (Finset.mem_univ _)
      · exact Real.rpow_le_rpow_of_exponent_le (integralFractionalIdeals_absNorm_ge_one J) (neg_le_neg (le_of_lt (show t < z.re from hz)))
      · exact Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _
      · exact Finset.sum_nonneg (fun c _ => norm_nonneg (w c))
  exact (H.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hts)).differentiableWithinAt

 
lemma idealClassDirichlet_partition {K : Type*} [Field K] [NumberField K]
    (w : ClassGroup (𝓞 K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    idealClassDirichlet K w s = ∑ c : ClassGroup (𝓞 K), w c⁻¹ *
      ∑' J : integralIdealClassFiber (classRepresentative K c),
        ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ)^(-s) := by
  classical
  let F := fun J : integralFractionalIdeals K =>
    w (ClassGroup.mk K J.1) * ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ)^(-s)
  have H := ((idealClassPartitionEquiv K).summable_iff.mpr
    (idealClassDirichlet_summable w hs)).tsum_sigma
  change (∑' x, F (idealClassPartitionEquiv K x)) = _ at H
  rw [(idealClassPartitionEquiv K).tsum_eq F] at H
  simp only [tsum_fintype] at H
  rw [idealClassDirichlet, show (∑' J, F J) = _ from H]
  apply Finset.sum_congr rfl
  intro c _
  change (∑' J : integralIdealClassFiber (classRepresentative K c),
    w (ClassGroup.mk K J.1) * ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ)^(-s)) = _
  simp_rw [show ∀ J : integralIdealClassFiber (classRepresentative K c),
    ClassGroup.mk K J.1 = c⁻¹ from fun J => by rw [J.2.2,classRepresentative_spec]]
  exact tsum_mul_left


end
end ArtinMatthews.VaryingKummerAnalytic

