module

public import ArtinMatthews.VaryingKummerAnalyticDedekindSeriesPartial


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine complex partial ideal-class series in arbitrary signature. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Set
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section

/-- Every actual nonzero integral fractional ideal has absolute norm at least one. -/
theorem integralFractionalIdeals_absNorm_ge_one {K : Type*} [Field K] [NumberField K]
    (J : integralFractionalIdeals K) :
    1 ≤ (FractionalIdeal.absNorm J.1.val : ℝ) := by
  obtain ⟨I, hI⟩ := (integralFractionalIdealsEquiv K).surjective J
  subst J
  change 1 ≤ (FractionalIdeal.absNorm (I.1 : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
  rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
    (by simpa only [ne_eq, Ideal.absNorm_eq_zero_iff] using I.2))

variable (K : Type*) [Field K] [NumberField K]

/-- Actual complex Dirichlet series over the specified integral ideal class. -/
def mixedPartialDedekindDirichlet (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  ∑' J : integralIdealClassFiber I,
    ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ) ^ (-s)

theorem mixedPartialDedekindDirichlet_summable
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : integralIdealClassFiber I =>
      ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ) ^ (-s)) := by
  apply Summable.of_norm_bounded (mixedPartialDedekind_norm_summable K I hs)
  intro J
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos J.val),
    Complex.neg_re]

theorem mixedPartialDedekindDirichlet_differentiableOn
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    DifferentiableOn ℂ (mixedPartialDedekindDirichlet K I) {s : ℂ | 1 < s.re} := by
  intro s hs
  obtain ⟨t, ht, hts⟩ := exists_between (show 1 < s.re from hs)
  have h : DifferentiableOn ℂ (mixedPartialDedekindDirichlet K I)
      {z : ℂ | t < z.re} := by
    change DifferentiableOn ℂ (fun z : ℂ => ∑' J : integralIdealClassFiber I,
      ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ) ^ (-z)) _
    apply Complex.differentiableOn_tsum_of_summable_norm
      (mixedPartialDedekind_norm_summable K I ht)
    · intro J
      apply Differentiable.differentiableOn
      apply Differentiable.const_cpow (differentiable_id.neg)
      exact Or.inl (Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos J.val).ne')
    · exact isOpen_lt continuous_const Complex.continuous_re
    · intro J z hz
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos J.val),
        Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le
        (integralFractionalIdeals_absNorm_ge_one ⟨J.val, J.property.1⟩)
        (neg_le_neg (le_of_lt (show t < z.re from hz)))
  exact (h.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hts)).differentiableWithinAt

theorem mixedPartialDedekindDirichlet_analyticOnNhd
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    AnalyticOnNhd ℂ (mixedPartialDedekindDirichlet K I) {s : ℂ | 1 < s.re} :=
  (mixedPartialDedekindDirichlet_differentiableOn K I).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

/-- The complex series has exactly the actual positive real norm series on
its real axis, rather than an assumed interpolation identity. -/
theorem mixedPartialDedekindDirichlet_ofReal
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    mixedPartialDedekindDirichlet K I (r : ℂ) =
      ((∑' J : integralIdealClassFiber I,
        (FractionalIdeal.absNorm J.1.val : ℝ) ^ (-r) : ℝ) : ℂ) := by
  unfold mixedPartialDedekindDirichlet
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro J
  simpa only [Complex.ofReal_neg] using
    (Complex.ofReal_cpow (fractionalIdeal_absNorm_pos J.val).le (-r)).symm

/-- The real-axis complex class series agrees with the actual ENNReal series
used in the mixed theta Mellin identity. -/
theorem mixedPartialDedekindDirichlet_positive
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {r : ℝ} (hr : 1 < r) :
    ENNReal.ofReal ((mixedPartialDedekindDirichlet K I (r : ℂ)).re) =
      mixedPartialDedekindPositive K I r := by
  rw [mixedPartialDedekindDirichlet_ofReal, Complex.ofReal_re,
    mixedPartialDedekindPositive,
    ENNReal.ofReal_tsum_of_nonneg
      (fun J : integralIdealClassFiber I =>
        Real.rpow_nonneg (fractionalIdeal_absNorm_pos J.val).le _)
      (mixedPartialDedekind_norm_summable K I hr)]

/-- The precise real-axis value used to pass from the positive Mellin
identity to its complex partial completion. -/
theorem mixedPartialDedekindDirichlet_ofReal_toReal
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {r : ℝ} (hr : 1 < r) :
    mixedPartialDedekindDirichlet K I (r : ℂ) =
      ((mixedPartialDedekindPositive K I r).toReal : ℂ) := by
  have heq := (mixedPartialDedekindDirichlet_positive K I hr).symm
  rw [mixedPartialDedekindDirichlet_ofReal, Complex.ofReal_re] at heq
  rw [mixedPartialDedekindDirichlet_ofReal, heq,
    ENNReal.toReal_ofReal (tsum_nonneg (fun J : integralIdealClassFiber I =>
      Real.rpow_nonneg (fractionalIdeal_absNorm_pos J.val).le _))]

end
end ArtinMatthews.VaryingKummerAnalytic
