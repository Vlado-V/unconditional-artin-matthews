module

public import ArtinMatthews.SourceComplexProductTest
public import ArtinMatthews.SourceComplexTraceInversion
public import ArtinMatthews.SourceComplexZetaIntegrability
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem source_complex_product_trace_inversion (f : ι → 𝓢(ℂ, ℂ)) (x : ι → ℂ) :
    sourceComplexProductFourier
      (sourceComplexProductFourier (fun y : ι → ℂ => ∏ i, f i (y i))) x =
        ∏ i, f i (-x i) := by
  rw [show sourceComplexProductFourier (fun y : ι → ℂ => ∏ i, f i (y i)) =
      (fun y => ∏ i, sourceComplexTraceFourier (f i) (y i)) from
    funext (source_complex_product_fourier_tensor (fun i => f i))]
  rw [source_complex_product_fourier_tensor]
  simp_rw [source_complex_trace_inversion]

theorem source_complex_trace_physical_pairing_nonzero :
    (∫ z : ℂ, sourceAnnularSchwartzTest z * (‖z‖ ^ (-(1 / 3 : ℝ)) : ℝ)
      ∂sourceComplexTraceMeasure) ≠ 0 := by
  unfold sourceComplexTraceMeasure
  rw [integral_smul_measure]
  exact smul_ne_zero (by norm_num) sourceAnnularSchwartzTest_weighted_nonzero

theorem source_complex_trace_physical_pairing_integrable :
    Integrable (fun z : ℂ => sourceAnnularSchwartzTest z *
      (‖z‖ ^ (-(1 / 3 : ℝ)) : ℝ)) sourceComplexTraceMeasure := by
  exact (source_complex_schwartz_weighted_integrable sourceAnnularSchwartzTest
    (1 / 3) (by norm_num) (by norm_num)).smul_measure (by norm_num : (2 : ENNReal) ≠ ⊤)

theorem sourceComplexProductTest_physical_pairing_integrable :
    Integrable (fun y : ι → ℂ => sourceComplexProductTest y *
      ∏ i, ((‖y i‖ ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ)) (sourceComplexProductMeasure ι) := by
  unfold sourceComplexProductTest
  simp_rw [← Finset.prod_mul_distrib]
  exact Integrable.fintype_prod (fun _ => source_complex_trace_physical_pairing_integrable)

theorem sourceComplexProductTest_physical_pairing_nonzero :
    (∫ y : ι → ℂ, sourceComplexProductTest y *
      ∏ i, ((‖y i‖ ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) ∂sourceComplexProductMeasure ι) ≠ 0 := by
  unfold sourceComplexProductTest
  simp_rw [← Finset.prod_mul_distrib]
  rw [sourceComplexProductMeasure, integral_fintype_prod_eq_prod
    (fun (_ : ι) (z : ℂ) => sourceAnnularSchwartzTest z *
      ((‖z‖ ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ))]
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => source_complex_trace_physical_pairing_nonzero)

theorem source_complex_five_sixths_density_all (z : ℂ) :
    (‖z‖ ^ 2) ^ (5 / 6 : ℝ) / ‖z‖ ^ 2 = ‖z‖ ^ (-(1 / 3 : ℝ)) := by
  by_cases hz : z = 0
  · simp [hz]
  · exact source_complex_five_sixths_density z hz

theorem source_complex_product_five_sixths_density (x : ι → ℂ) :
    sourceComplexProductAbsoluteValue x ^ (5 / 6 : ℝ) / sourceComplexProductAbsoluteValue x =
      ∏ i, ‖x i‖ ^ (-(1 / 3 : ℝ)) := by
  unfold sourceComplexProductAbsoluteValue
  rw [← Real.finsetProd_rpow _ _ (fun i _ => sq_nonneg ‖x i‖), ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl (fun i _ => source_complex_five_sixths_density_all (x i))

theorem sourceComplexProductTest_actual_physical_mellin_nonzero :
    (∫ y : ι → ℂ, sourceComplexProductTest y *
      (sourceComplexProductAbsoluteValue y ^ (5 / 6 : ℝ) /
        sourceComplexProductAbsoluteValue y : ℝ) ∂sourceComplexProductMeasure ι) ≠ 0 := by
  simp_rw [source_complex_product_five_sixths_density, Complex.ofReal_prod]
  exact sourceComplexProductTest_physical_pairing_nonzero

end
end ArtinMatthews.VaryingKummerAnalytic
