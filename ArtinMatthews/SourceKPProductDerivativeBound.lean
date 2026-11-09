module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Relative derivative bounds multiply without dividing by any
factor, including at zeros of the product. -/

namespace ArtinMatthews
open scoped BigOperators

theorem sourceKPFinitePi_comp_norm_le {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E →L[ℝ] ℂ) (i : ι) :
    ‖L.comp (ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E)‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro x
  change ‖L (x i)‖ ≤ ‖L‖*‖x‖
  exact (L.le_opNorm (x i)).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg L))

theorem sourceKPFinitePi_comp_fderiv_bound {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℂ) (x : ι → E) (i : ι)
    (hf : DifferentiableAt ℝ f (x i)) (a : ℝ)
    (ha : ‖fderiv ℝ f (x i)‖ ≤ a*‖f (x i)‖) :
    ‖fderiv ℝ (fun y : ι → E => f (y i)) x‖ ≤ a*‖f (x i)‖ := by
  have hd := hf.hasFDerivAt.comp x (hasFDerivAt_apply (𝕜 := ℝ) i x)
  have he : fderiv ℝ (fun y : ι → E => f (y i)) x =
      (fderiv ℝ f (x i)).comp (ContinuousLinearMap.proj i) := by
    simpa only [Function.comp_def] using hd.fderiv
  rw [he]
  exact (sourceKPFinitePi_comp_norm_le (ι := ι) (E := E) (fderiv ℝ f (x i)) i).trans ha

theorem sourceKPFiniteProduct_fderiv_bound {ι E : Type*} [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Finset ι) (f : ι → E → ℂ) (a : ι → ℝ) (x : E)
    (hf : ∀ i ∈ I, DifferentiableAt ℝ (f i) x)
    (hbound : ∀ i ∈ I, ‖fderiv ℝ (f i) x‖ ≤ a i*‖f i x‖) :
    ‖fderiv ℝ (fun y => ∏ i ∈ I, f i y) x‖ ≤
      (∑ i ∈ I, a i)*‖∏ i ∈ I, f i x‖ := by
  rw [fderiv_finsetProd hf]
  calc
    ‖∑ i ∈ I, (∏ j ∈ I.erase i, f j x) • fderiv ℝ (f i) x‖ ≤
        ∑ i ∈ I, ‖(∏ j ∈ I.erase i, f j x) • fderiv ℝ (f i) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ I, a i*‖∏ j ∈ I, f j x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul]
      have hp : ‖∏ j ∈ I.erase i, f j x‖*‖f i x‖ = ‖∏ j ∈ I, f j x‖ := by
        rw [← norm_mul,Finset.prod_erase_mul I (fun j => f j x) hi]
      calc
        ‖∏ j ∈ I.erase i, f j x‖*‖fderiv ℝ (f i) x‖ ≤
            ‖∏ j ∈ I.erase i, f j x‖*(a i*‖f i x‖) :=
          mul_le_mul_of_nonneg_left (hbound i hi) (norm_nonneg _)
        _ = a i*‖∏ j ∈ I, f j x‖ := by rw [← hp]; ring
    _ = _ := (Finset.sum_mul I a _).symm

end ArtinMatthews
