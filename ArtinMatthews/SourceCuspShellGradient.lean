module

public import ArtinMatthews.SourceCuspShellBump
public import ArtinMatthews.SourceHyperbolicProductEnergy
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv


set_option backward.privateInPublic true
@[expose] public section

/-! Exact hyperbolic gradient energy of the genuine logarithmic shell cutoff. -/
namespace ArtinMatthews
open OAI.CubicEisenstein SourceHyperbolicGreen
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

def sourceProductHeightProjection (i : ι) : ProductSpace ι →L[ℝ] ℝ :=
  Complex.reCLM.comp (productHeightCLM i)

omit [Fintype ι] in
theorem sourceProductHeightProjection_apply (i : ι) (p : ProductSpace ι) :
    sourceProductHeightProjection i p = p i 2 := rfl

omit [Fintype ι] in
theorem sourceProductHeightProjection_direction (k i : ι) (j : Fin 3) :
    sourceProductHeightProjection k (productDirection i j) =
      if k = i then if j = 2 then 1 else 0 else 0 := by
  rw [sourceProductHeightProjection_apply]
  simp only [productDirection]
  by_cases hk : k = i
  · subst k
    rw [Pi.single_eq_same]
    simp [euclideanCoordinateVector, eq_comm]
  · rw [Pi.single_eq_of_ne hk]
    simp only [hk, ite_false]
    rfl

def sourceProductLogHeight (C : ℝ) (p : ProductSpace ι) : ℝ :=
  Real.log C + ∑ i, 2 * Real.log (p i 2)

theorem sourceProductLogHeight_eq (C : ℝ) (hC : 0 < C)
    (p : ProductSpace ι) (hp : p ∈ productUpper ι) :
    sourceProductLogHeight C p = Real.log (C * ∏ i, (p i 2) ^ 2) := by
  have hprod : (∏ i, (p i 2) ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero 2 (productUpper_pos hp i).ne')
  rw [Real.log_mul hC.ne' hprod, Real.log_prod (fun i _ => pow_ne_zero 2 (productUpper_pos hp i).ne')]
  simp only [sourceProductLogHeight, Real.log_pow, Nat.cast_ofNat]

theorem sourceProductLogHeight_hasFDerivAt (C : ℝ)
    (p : ProductSpace ι) (hp : p ∈ productUpper ι) :
    HasFDerivAt (sourceProductLogHeight C)
      (∑ i, (2 / (p i 2)) • sourceProductHeightProjection i) p := by
  have hi (i : ι) : HasFDerivAt (fun q : ProductSpace ι => 2 * Real.log (q i 2))
      ((2 / (p i 2)) • sourceProductHeightProjection i) p := by
    have h := ((Real.hasDerivAt_log (productUpper_pos hp i).ne').comp_hasFDerivAt p
      (sourceProductHeightProjection i).hasFDerivAt).const_mul 2
    convert h using 1
    · rfl
    · simp only [div_eq_mul_inv, smul_smul]
  exact (HasFDerivAt.fun_sum (fun i _ => hi i)).const_add (Real.log C)

theorem sourceProductLogHeight_contDiffAt (C : ℝ)
    (p : ProductSpace ι) (hp : p ∈ productUpper ι) :
    ContDiffAt ℝ ∞ (sourceProductLogHeight C) p := by
  apply contDiffAt_const.add
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_const.mul
    ((sourceProductHeightProjection i).contDiff.contDiffAt.log (productUpper_pos hp i).ne')

def sourceProductShellCutoff (C a : ℝ) (p : ProductSpace ι) : ℝ :=
  sourceCuspShellBump (sourceProductLogHeight C p - a)

theorem sourceProductShellCutoff_contDiffAt (C a : ℝ)
    (p : ProductSpace ι) (hp : p ∈ productUpper ι) :
    ContDiffAt ℝ ∞ (sourceProductShellCutoff C a) p :=
  sourceCuspShellBump_contDiff.contDiffAt.comp p
    ((sourceProductLogHeight_contDiffAt C p hp).sub contDiffAt_const)

theorem sourceProductShellCutoff_partial (C a : ℝ)
    (p : ProductSpace ι) (hp : p ∈ productUpper ι) (i : ι) (j : Fin 3) :
    productPartial (fun q => (sourceProductShellCutoff C a q : ℂ)) i j p =
      if j = 2 then ((2 * deriv sourceCuspShellBump (sourceProductLogHeight C p - a) / (p i 2) : ℝ) : ℂ)
      else 0 := by
  have hreal := (sourceCuspShellBump_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt.comp_hasFDerivAt p
    ((sourceProductLogHeight_hasFDerivAt C p hp).sub_const a)
  have hcomplex := Complex.ofRealCLM.hasFDerivAt.comp p hreal
  change HasFDerivAt (fun q => (sourceProductShellCutoff C a q : ℂ)) _ p at hcomplex
  rw [productPartial, hcomplex.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    sum_apply, sourceProductHeightProjection_direction]
  fin_cases j <;> simp
  ring

theorem sourceProductShellCutoff_energy (C a : ℝ)
    (p : ProductSpace ι) (hp : p ∈ productUpper ι) :
    productGradientEnergy (fun q => (sourceProductShellCutoff C a q : ℂ)) p =
      4 * Fintype.card ι * (deriv sourceCuspShellBump (sourceProductLogHeight C p - a)) ^ 2 := by
  have hi (i : ι) : (p i 2) ^ 2 *
      (∑ j : Fin 3, ‖productPartial (fun q => (sourceProductShellCutoff C a q : ℂ)) i j p‖ ^ 2) =
        4 * (deriv sourceCuspShellBump (sourceProductLogHeight C p - a)) ^ 2 := by
    simp only [sourceProductShellCutoff_partial C a p hp i, Fin.sum_univ_three]
    norm_num only [Fin.reduceEq, ite_false, ite_true, norm_zero, zero_pow, zero_add,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    field_simp [(productUpper_pos hp i).ne']
    ring
  simp only [productGradientEnergy, hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem sourceProductShellCutoff_energy_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (C a : ℝ) (p : ProductSpace ι), p ∈ productUpper ι →
      productGradientEnergy (fun q => (sourceProductShellCutoff C a q : ℂ)) p ≤
        4 * Fintype.card ι * B ^ 2 := by
  obtain ⟨B, hB, hbound⟩ := sourceCuspShellBump_deriv_bound
  refine ⟨B, hB, ?_⟩
  intro C a p hp
  rw [sourceProductShellCutoff_energy C a p hp]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := hbound (sourceProductLogHeight C p - a)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [Real.norm_eq_abs, sq_abs] using hs

end
end ArtinMatthews
