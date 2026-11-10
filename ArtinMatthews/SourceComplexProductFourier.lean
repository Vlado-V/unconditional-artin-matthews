module

public import ArtinMatthews.SourceAnnularFourierTest
public import ArtinMatthews.SourceComplexTraceFourier
public import ArtinMatthews.SourceComplexTraceNonvanishing
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.MeasureTheory.Integral.Pi
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

instance sourceComplexTraceMeasure_sigmaFinite : SigmaFinite sourceComplexTraceMeasure := by
  change SigmaFinite ((2 : NNReal) • (volume : Measure ℂ))
  infer_instance

def sourceComplexProductMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℂ) :=
  Measure.pi (fun _ : ι => sourceComplexTraceMeasure)

def sourceComplexProductFourier (f : (ι → ℂ) → ℂ) (y : ι → ℂ) : ℂ :=
  ∫ x : ι → ℂ, Real.fourierChar (-(∑ i, 2 * (x i * y i).re)) • f x
    ∂sourceComplexProductMeasure ι

theorem source_complex_product_phase (x y : ι → ℂ) :
    Real.fourierChar (-(∑ i, 2 * (x i * y i).re)) =
      ∏ i, Real.fourierChar (-(2 * (x i * y i).re)) := by
  classical
  have h (s : Finset ι) : Real.fourierChar (-(∑ i ∈ s, 2 * (x i * y i).re)) =
      ∏ i ∈ s, Real.fourierChar (-(2 * (x i * y i).re)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi hs =>
      simp only [Finset.sum_insert hi, Finset.prod_insert hi, neg_add,
        AddChar.map_add_eq_mul, hs]
  exact h Finset.univ

/-- The actual trace integral of a pure tensor factors into the actual local transforms. -/
theorem source_complex_product_fourier_tensor (f : ι → ℂ → ℂ) (y : ι → ℂ) :
    sourceComplexProductFourier (fun x => ∏ i, f i (x i)) y =
      ∏ i, sourceComplexTraceFourier (f i) (y i) := by
  unfold sourceComplexProductFourier sourceComplexProductMeasure sourceComplexTraceFourier
  have hi (x : ι → ℂ) :
      Real.fourierChar (-(∑ i, 2 * (x i * y i).re)) • (∏ i, f i (x i)) =
        ∏ i, Real.fourierChar (-(2 * (x i * y i).re)) • f i (x i) := by
    rw [Circle.smul_def, source_complex_product_phase]
    rw [show ((∏ i, Real.fourierChar (-(2 * (x i * y i).re)) : Circle) : ℂ) =
      ∏ i, (Real.fourierChar (-(2 * (x i * y i).re)) : ℂ) from
        map_prod Circle.coeHom _ _]
    simp only [Circle.smul_def]
    exact Finset.prod_mul_distrib.symm
  simp_rw [hi]
  exact integral_fintype_prod_eq_prod (μ := fun _ : ι => sourceComplexTraceMeasure)
    (fun i z => Real.fourierChar (-(2 * (z * y i).re)) • f i z)

def sourceComplexProductTest (x : ι → ℂ) : ℂ := ∏ i, sourceAnnularSchwartzTest (x i)

theorem sourceComplexProductTest_integrable :
    Integrable (sourceComplexProductTest (ι := ι)) (sourceComplexProductMeasure ι) := by
  exact Integrable.fintype_prod (fun _ =>
    sourceAnnularSchwartzTest.integrable.smul_measure (by norm_num : (2 : ENNReal) ≠ ⊤))

theorem sourceComplexProductTest_fourier_tensor (y : ι → ℂ) :
    sourceComplexProductFourier sourceComplexProductTest y =
      ∏ i, sourceComplexTraceFourier sourceAnnularSchwartzTest (y i) :=
  source_complex_product_fourier_tensor (fun _ => sourceAnnularSchwartzTest) y

theorem sourceComplexProductTest_fourier_zero [Nonempty ι] :
    sourceComplexProductFourier (sourceComplexProductTest (ι := ι)) 0 = 0 := by
  rw [sourceComplexProductTest_fourier_tensor]
  simp only [Pi.zero_apply, sourceAnnularSchwartzTest_trace_fourier_zero]
  simp

theorem sourceComplexProductTest_trace_mellin_integrable :
    Integrable (fun y : ι → ℂ => sourceComplexProductFourier sourceComplexProductTest y *
      ∏ i, ((‖y i‖ ^ (-(5 / 3 : ℝ)) : ℝ) : ℂ)) (sourceComplexProductMeasure ι) := by
  simp_rw [sourceComplexProductTest_fourier_tensor, ← Finset.prod_mul_distrib]
  exact Integrable.fintype_prod (fun _ => sourceAnnularSchwartzTest_trace_mellin_integrable)

theorem sourceComplexProductTest_trace_mellin_nonzero :
    (∫ y : ι → ℂ, sourceComplexProductFourier sourceComplexProductTest y *
      ∏ i, ((‖y i‖ ^ (-(5 / 3 : ℝ)) : ℝ) : ℂ) ∂sourceComplexProductMeasure ι) ≠ 0 := by
  simp_rw [sourceComplexProductTest_fourier_tensor, ← Finset.prod_mul_distrib]
  rw [sourceComplexProductMeasure, integral_fintype_prod_eq_prod
    (fun (_ : ι) (z : ℂ) => sourceComplexTraceFourier sourceAnnularSchwartzTest z *
      ((‖z‖ ^ (-(5 / 3 : ℝ)) : ℝ) : ℂ))]
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => sourceAnnularSchwartzTest_trace_mellin_nonzero)

end
end ArtinMatthews.VaryingKummerAnalytic
