module

public import ArtinMatthews.SourceComplexProductFourier


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Set
open scoped BigOperators FourierTransform SchwartzMap ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem sourceComplexProductTest_smooth :
    ContDiff ℝ ∞ (sourceComplexProductTest (ι := ι)) := by
  exact contDiff_prod (fun i _ => (sourceAnnularSchwartzTest.smooth ⊤).comp (contDiff_apply ℝ ℂ i))

theorem sourceComplexProductTest_support_subset :
    Function.support (sourceComplexProductTest (ι := ι)) ⊆
      Set.pi univ (fun _ : ι => tsupport (sourceAnnularSchwartzTest : ℂ → ℂ)) := by
  intro x hx i _
  apply subset_tsupport
  exact Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ i)

theorem sourceComplexProductTest_compact :
    HasCompactSupport (sourceComplexProductTest (ι := ι)) := by
  have h : HasCompactSupport (sourceAnnularSchwartzTest : ℂ → ℂ) :=
    sourceAnnularComplexTest_compact
  exact HasCompactSupport.of_support_subset_isCompact
    (isCompact_univ_pi (fun _ : ι => h)) sourceComplexProductTest_support_subset

theorem sourceComplexProductTest_tsupport_subset :
    tsupport (sourceComplexProductTest (ι := ι)) ⊆
      Set.pi univ (fun _ : ι => tsupport (sourceAnnularSchwartzTest : ℂ → ℂ)) := by
  have h : HasCompactSupport (sourceAnnularSchwartzTest : ℂ → ℂ) :=
    sourceAnnularComplexTest_compact
  exact closure_minimal sourceComplexProductTest_support_subset
    (isCompact_univ_pi (fun _ : ι => h)).isClosed

theorem sourceComplexProductTest_away_coordinate_zero :
    tsupport (sourceComplexProductTest (ι := ι)) ⊆ {x | ∀ i, x i ≠ 0} := by
  intro x hx i
  exact sourceAnnularSchwartzTest_away_zero (sourceComplexProductTest_tsupport_subset hx i trivial)

def sourceComplexProductSchwartzTest : 𝓢(ι → ℂ, ℂ) :=
  sourceComplexProductTest_compact.toSchwartzMap sourceComplexProductTest_smooth

theorem sourceComplexProductSchwartzTest_apply (x : ι → ℂ) :
    sourceComplexProductSchwartzTest x = ∏ i, sourceAnnularSchwartzTest (x i) := rfl

def sourceComplexProductAbsoluteValue (x : ι → ℂ) : ℝ := ∏ i, ‖x i‖ ^ 2

theorem source_complex_one_sixth_density_all (z : ℂ) :
    (‖z‖ ^ 2) ^ (1 / 6 : ℝ) / ‖z‖ ^ 2 = ‖z‖ ^ (-(5 / 3 : ℝ)) := by
  by_cases hz : z = 0
  · simp [hz, Real.zero_rpow (by norm_num : -(5 / 3 : ℝ) ≠ 0)]
  · exact source_complex_one_sixth_density z hz

theorem source_complex_product_one_sixth_density (x : ι → ℂ) :
    sourceComplexProductAbsoluteValue x ^ (1 / 6 : ℝ) / sourceComplexProductAbsoluteValue x =
      ∏ i, ‖x i‖ ^ (-(5 / 3 : ℝ)) := by
  unfold sourceComplexProductAbsoluteValue
  rw [← Real.finsetProd_rpow _ _ (fun i _ => sq_nonneg ‖x i‖), ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl (fun i _ => source_complex_one_sixth_density_all (x i))

theorem sourceComplexProductTest_actual_mellin_nonzero :
    (∫ y : ι → ℂ, sourceComplexProductFourier sourceComplexProductTest y *
      (sourceComplexProductAbsoluteValue y ^ (1 / 6 : ℝ) /
        sourceComplexProductAbsoluteValue y : ℝ) ∂sourceComplexProductMeasure ι) ≠ 0 := by
  simp_rw [source_complex_product_one_sixth_density, Complex.ofReal_prod]
  exact sourceComplexProductTest_trace_mellin_nonzero

end
end ArtinMatthews.VaryingKummerAnalytic
