module

public import ArtinMatthews.SourceCuspShellGradient
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Normed.Group.Bounded


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Filter SourceHyperbolicGreen
open scoped Topology ContDiff BigOperators Classical
noncomputable section

theorem sourceSmoothTransition_deriv_tsupport :
    tsupport (deriv Real.smoothTransition) ⊆ Icc 0 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra h
    have hlt : x < 0 := lt_of_not_ge h
    have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [gt_mem_nhds hlt] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    exact hx (by rw [he.deriv_eq]; simp)
  · by_contra h
    have hlt : 1 < x := lt_of_not_ge h
    have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [lt_mem_nhds hlt] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    exact hx (by rw [he.deriv_eq]; simp)

theorem sourceSmoothTransition_deriv_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ t, ‖deriv Real.smoothTransition t‖ ≤ B := by
  have hs : HasCompactSupport (deriv Real.smoothTransition) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) sourceSmoothTransition_deriv_tsupport
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (2 : ℕ∞))).continuous_deriv (by norm_num)
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun t => (hB t).trans (le_max_right _ _)⟩

variable {ι : Type*} [Fintype ι]

def sourceProductSmoothExhaustion (C a : ℝ) (p : ProductSpace ι) : ℝ :=
  1 - Real.smoothTransition (sourceProductLogHeight C p - a)

theorem sourceProductSmoothExhaustion_contDiffAt (C a : ℝ)
    (p : ProductSpace ι) (hp : p ∈ productUpper ι) :
    ContDiffAt ℝ ∞ (sourceProductSmoothExhaustion C a) p := by
  exact contDiffAt_const.sub (Real.smoothTransition.contDiffAt.comp p
    ((sourceProductLogHeight_contDiffAt C p hp).sub contDiffAt_const))

theorem sourceProductSmoothExhaustion_partial (C a : ℝ)
    (p : ProductSpace ι) (hp : p ∈ productUpper ι) (i : ι) (j : Fin 3) :
    productPartial (fun q => (sourceProductSmoothExhaustion C a q : ℂ)) i j p =
      if j = 2 then
        ((-(2 * deriv Real.smoothTransition (sourceProductLogHeight C p - a) /
          (p i 2)) : ℝ) : ℂ)
      else 0 := by
  have hreal := (hasDerivAt_const (sourceProductLogHeight C p - a) (1 : ℝ)).sub
    ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable
      (by norm_num)).differentiableAt.hasDerivAt
  have hreal := hreal.comp_hasFDerivAt p
    ((sourceProductLogHeight_hasFDerivAt C p hp).sub_const a)
  have hcomplex := Complex.ofRealCLM.hasFDerivAt.comp p hreal
  change HasFDerivAt (fun q => (sourceProductSmoothExhaustion C a q : ℂ)) _ p at hcomplex
  rw [productPartial, hcomplex.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    sum_apply, sourceProductHeightProjection_direction]
  fin_cases j <;> simp
  ring

theorem sourceProductSmoothExhaustion_energy (C a : ℝ)
    (p : ProductSpace ι) (hp : p ∈ productUpper ι) :
    productGradientEnergy (fun q => (sourceProductSmoothExhaustion C a q : ℂ)) p =
      4 * Fintype.card ι *
        (deriv Real.smoothTransition (sourceProductLogHeight C p - a)) ^ 2 := by
  have hi (i : ι) : (p i 2) ^ 2 *
      (∑ j : Fin 3,
        ‖productPartial (fun q => (sourceProductSmoothExhaustion C a q : ℂ)) i j p‖ ^ 2) =
        4 * (deriv Real.smoothTransition (sourceProductLogHeight C p - a)) ^ 2 := by
    simp only [sourceProductSmoothExhaustion_partial C a p hp i, Fin.sum_univ_three]
    norm_num only [Fin.reduceEq, ite_false, ite_true, norm_zero, zero_pow, zero_add,
      Complex.norm_real, Real.norm_eq_abs, abs_neg, sq_abs]
    field_simp [(productUpper_pos hp i).ne']
    ring
  simp only [productGradientEnergy, hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem sourceProductSmoothExhaustion_energy_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (C a : ℝ) (p : ProductSpace ι), p ∈ productUpper ι →
      productGradientEnergy (fun q => (sourceProductSmoothExhaustion C a q : ℂ)) p ≤
        4 * Fintype.card ι * B ^ 2 := by
  obtain ⟨B, hB, hbound⟩ := sourceSmoothTransition_deriv_bound
  refine ⟨B, hB, ?_⟩
  intro C a p hp
  rw [sourceProductSmoothExhaustion_energy C a p hp]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hbound (sourceProductLogHeight C p - a)) 2
  simpa only [Real.norm_eq_abs, sq_abs] using hs

end
end ArtinMatthews
