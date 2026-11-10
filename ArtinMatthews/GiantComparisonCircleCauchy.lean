module

public import ArtinMatthews.GiantComparisonCirclePairing
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import ArtinMatthews.MarkedMinorArcProductOperator


set_option backward.privateInPublic true
@[expose] public section

/-! Major and minor energy bounds on a real fundamental interval for the
normalized unit circle. The measurable major set may overlap its translates
before restriction to the fundamental interval. -/
namespace ArtinMatthews
open MeasureTheory AddCircle Set
open scoped BigOperators ComplexConjugate ENNReal
noncomputable section
local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩

local notation "Circle1" => AddCircle (1:ℝ)
local notation "haar" => @AddCircle.haarAddCircle (1:ℝ) _
local notation "unitMeasure" => volume.restrict (Ioc (0:ℝ) 1)

/-- Normalized unit-circle integration on the literal real fundamental cell. -/
theorem giantComparisonCircle_integral_Ioc {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Circle1 → E) :
    (∫ θ : Circle1, F θ ∂haar) = ∫ t : ℝ in Ioc (0:ℝ) 1, F (t:Circle1) := by
  rw [AddCircle.integral_haarAddCircle,inv_one,one_smul]
  simpa only [zero_add] using (AddCircle.integral_preimage (1:ℝ) 0 F).symm

private theorem comparisonCircle_lift_memLp {u : Circle1 → ℂ} (hu : Continuous u) :
    MemLp (fun t : ℝ => u (t:Circle1)) 2 unitMeasure := by
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hu.continuousOn
  have hl := hu.comp (AddCircle.continuous_mk' (1:ℝ))
  exact MemLp.of_bound hl.aestronglyMeasurable M (Filter.Eventually.of_forall
    fun t => hM (t:Circle1) (mem_univ _))

private theorem comparisonCircle_lift_integrable {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : Continuous f) : Integrable f unitMeasure :=
  hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem comparisonCircle_pairing_cauchy {μ : Measure ℝ} {m u v : ℝ → ℂ}
    {C : ℝ} (hC : 0 ≤ C) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hF : Integrable (fun t => m t*conj (u t)*v t) μ)
    (hprod : Integrable (fun t => ‖u t‖*‖v t‖) μ)
    (hm : ∀ᵐ t ∂μ, ‖m t‖ ≤ C) :
    ‖∫ t, m t*conj (u t)*v t ∂μ‖ ≤
      C*Real.sqrt ((∫ t, ‖u t‖^2 ∂μ)*(∫ t, ‖v t‖^2 ∂μ)) := by
  have hu' : MemLp u (ENNReal.ofReal (2:ℝ)) μ := by simpa using hu
  have hv' : MemLp v (ENNReal.ofReal (2:ℝ)) μ := by simpa using hv
  have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hu' hv'
  simp only [Real.rpow_two,← Real.sqrt_eq_rpow] at hholder
  have hu0 : 0 ≤ ∫ t, ‖u t‖^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hpoint : ∀ᵐ t ∂μ, ‖m t*conj (u t)*v t‖ ≤ C*(‖u t‖*‖v t‖) := by
    filter_upwards [hm] with t ht
    rw [norm_mul,norm_mul,Complex.norm_conj,mul_assoc]
    exact mul_le_mul_of_nonneg_right ht (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    _ ≤ ∫ t, ‖m t*conj (u t)*v t‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, C*(‖u t‖*‖v t‖) ∂μ := integral_mono_ae hF.norm (hprod.const_mul C) hpoint
    _ ≤ _ := by
      rw [integral_const_mul,Real.sqrt_mul hu0]
      exact mul_le_mul_of_nonneg_left hholder hC

/-- The exact circle pairing, split by a measurable major set on `(0,1]`.
Only the left polynomial needs a local major-arc energy estimate. -/
theorem giantComparisonCircle_major_minor_bound
    (m : Circle1 → ℂ) (hm : Continuous m) (S T : Finset ℤ) (U : S → ℂ) (V : T → ℂ)
    (major : Set ℝ) (hmajor : MeasurableSet major) {δ E : ℝ} (hδ : 0 ≤ δ)
    (hunit : ∀ θ, ‖m θ‖ ≤ 1)
    (hminor : ∀ t ∈ Ioc (0:ℝ) 1, t ∉ major → ‖m (t:Circle1)‖ ≤ δ)
    (henergy : (∫ t in major, ‖markedProductFourierPolynomial S U (t:Circle1)‖^2
      ∂unitMeasure) ≤ E) :
    ‖∫ θ : Circle1, m θ*conj (markedProductFourierPolynomial S U θ)*
      markedProductFourierPolynomial T V θ ∂haar‖ ≤
      δ*Real.sqrt ((∑ u : S, ‖U u‖^2)*(∑ v : T, ‖V v‖^2)) +
        Real.sqrt ((∑ v : T, ‖V v‖^2)*E) := by
  let u (t : ℝ) := markedProductFourierPolynomial S U (t:Circle1)
  let v (t : ℝ) := markedProductFourierPolynomial T V (t:Circle1)
  let m' (t : ℝ) := m (t:Circle1)
  let F (t : ℝ) := m' t*conj (u t)*v t
  have hcu : Continuous u := (markedProductFourierPolynomial S U).continuous.comp
    (AddCircle.continuous_mk' (1:ℝ))
  have hcv : Continuous v := (markedProductFourierPolynomial T V).continuous.comp
    (AddCircle.continuous_mk' (1:ℝ))
  have hcm : Continuous m' := hm.comp (AddCircle.continuous_mk' (1:ℝ))
  have hF : Integrable F unitMeasure :=
    comparisonCircle_lift_integrable ((hcm.mul hcu.star).mul hcv)
  have hprod : Integrable (fun t => ‖u t‖*‖v t‖) unitMeasure :=
    comparisonCircle_lift_integrable (hcu.norm.mul hcv.norm)
  have hlu : MemLp u 2 unitMeasure := comparisonCircle_lift_memLp
    (markedProductFourierPolynomial S U).continuous
  have hlv : MemLp v 2 unitMeasure := comparisonCircle_lift_memLp
    (markedProductFourierPolynomial T V).continuous
  have hpu : (∫ t, ‖u t‖^2 ∂unitMeasure) = ∑ a : S, ‖U a‖^2 := by
    exact (giantComparisonCircle_integral_Ioc
      (fun θ => ‖markedProductFourierPolynomial S U θ‖^2)).symm.trans
        (markedProductFourierPolynomial_parseval S U)
  have hpv : (∫ t, ‖v t‖^2 ∂unitMeasure) = ∑ b : T, ‖V b‖^2 := by
    exact (giantComparisonCircle_integral_Ioc
      (fun θ => ‖markedProductFourierPolynomial T V θ‖^2)).symm.trans
        (markedProductFourierPolynomial_parseval T V)
  have hbu (A : Set ℝ) :
      (∫ t in A, ‖u t‖^2 ∂unitMeasure) ≤ ∑ a : S, ‖U a‖^2 := by
    rw [← hpu]
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (comparisonCircle_lift_integrable (hcu.norm.pow 2))
  have hbv (A : Set ℝ) :
      (∫ t in A, ‖v t‖^2 ∂unitMeasure) ≤ ∑ b : T, ‖V b‖^2 := by
    rw [← hpv]
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (comparisonCircle_lift_integrable (hcv.norm.pow 2))
  have hbound (A : Set ℝ) {C : ℝ} (hC : 0 ≤ C)
      (h : ∀ᵐ t ∂(unitMeasure).restrict A, ‖m' t‖ ≤ C) :
      ‖∫ t in A, F t ∂unitMeasure‖ ≤ C*Real.sqrt
        ((∫ t in A, ‖u t‖^2 ∂unitMeasure)*(∫ t in A, ‖v t‖^2 ∂unitMeasure)) :=
    comparisonCircle_pairing_cauchy hC (hlu.mono_measure Measure.restrict_le_self)
      (hlv.mono_measure Measure.restrict_le_self) hF.integrableOn hprod.integrableOn h
  have hmajorBound := hbound major zero_le_one (Filter.Eventually.of_forall fun t => hunit _)
  have hminorBound := hbound majorᶜ hδ (by
    filter_upwards [ae_restrict_mem hmajor.compl,
      ae_mono Measure.restrict_le_self (ae_restrict_mem measurableSet_Ioc)] with t ht hI
    exact hminor t hI ht)
  have hE : 0 ≤ E := (integral_nonneg fun _ => sq_nonneg _).trans henergy
  rw [giantComparisonCircle_integral_Ioc (fun θ => m θ*
    conj (markedProductFourierPolynomial S U θ)*markedProductFourierPolynomial T V θ)]
  change ‖∫ t, F t ∂unitMeasure‖ ≤ _
  rw [← integral_add_compl hmajor hF]
  calc
    _ ≤ ‖∫ t in major, F t ∂unitMeasure‖ + ‖∫ t in majorᶜ, F t ∂unitMeasure‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [add_comm]
      apply add_le_add
      · exact hminorBound.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
          (mul_le_mul (hbu _) (hbv _) (integral_nonneg fun _ => sq_nonneg _)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _))) hδ)
      · rw [one_mul] at hmajorBound
        apply hmajorBound.trans (Real.sqrt_le_sqrt _)
        rw [mul_comm (∑ v : T, ‖V v‖^2) E]
        exact mul_le_mul henergy (hbv _) (integral_nonneg fun _ => sq_nonneg _) hE

end
end ArtinMatthews
