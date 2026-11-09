module

public import ArtinMatthews.SourceArchimedeanProbeTest
public import ArtinMatthews.StandardAdelicArchTrace


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory NumberField NumberField.InfinitePlace
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def sourceComplexPlaceAdele
    (x : {v : InfinitePlace K // IsComplex v} → ℂ) : InfiniteAdeleRing K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (0, x)

theorem sourceComplexPlaceAdele_trace
    (x : {v : InfinitePlace K // IsComplex v} → ℂ) :
    StandardAdelic.archTrace K (sourceComplexPlaceAdele K x) = ∑ v, 2 * (x v).re := by
  change StandardAdelic.mixedTrace K
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (0, x))) = _
  rw [RingEquiv.apply_symm_apply]
  simp [StandardAdelic.mixedTrace]

theorem sourceComplexPlaceAdele_trace_mul
    (x y : {v : InfinitePlace K // IsComplex v} → ℂ) :
    StandardAdelic.archTrace K (sourceComplexPlaceAdele K x * sourceComplexPlaceAdele K y) =
      ∑ v, 2 * (x v * y v).re := by
  change StandardAdelic.mixedTrace K
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (0, x) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (0, y))) = _
  rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  simp [StandardAdelic.mixedTrace]

theorem sourceComplexPlaceAdele_character_mul
    (x y : {v : InfinitePlace K // IsComplex v} → ℂ) :
    StandardAdelic.archCharacter K (-(sourceComplexPlaceAdele K x * sourceComplexPlaceAdele K y)) =
      (Real.fourierChar (-(∑ v, 2 * (x v * y v).re)) : ℂ) := by
  change Complex.exp ((StandardAdelic.archTrace K
    (-(sourceComplexPlaceAdele K x * sourceComplexPlaceAdele K y)) : ℂ) * _) = _
  rw [map_neg, sourceComplexPlaceAdele_trace_mul, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- The Fourier operator written with the existing number-field archimedean character. -/
def sourceNumberFieldComplexFourier
    (f : ({v : InfinitePlace K // IsComplex v} → ℂ) → ℂ)
    (y : {v : InfinitePlace K // IsComplex v} → ℂ) : ℂ :=
  ∫ x, StandardAdelic.archCharacter K
    (-(sourceComplexPlaceAdele K x * sourceComplexPlaceAdele K y)) * f x
      ∂sourceComplexProductMeasure {v : InfinitePlace K // IsComplex v}

theorem sourceNumberFieldComplexFourier_eq
    (f : ({v : InfinitePlace K // IsComplex v} → ℂ) → ℂ)
    (y : {v : InfinitePlace K // IsComplex v} → ℂ) :
    sourceNumberFieldComplexFourier K f y = sourceComplexProductFourier f y := by
  unfold sourceNumberFieldComplexFourier sourceComplexProductFourier
  simp_rw [sourceComplexPlaceAdele_character_mul, Circle.smul_def, smul_eq_mul]

theorem sourceNumberFieldComplexFourier_test_mellin_nonzero :
    (∫ y : {v : InfinitePlace K // IsComplex v} → ℂ,
      sourceNumberFieldComplexFourier K sourceComplexProductTest y *
        (sourceComplexProductAbsoluteValue y ^ (1 / 6 : ℝ) /
          sourceComplexProductAbsoluteValue y : ℝ)
            ∂sourceComplexProductMeasure {v : InfinitePlace K // IsComplex v}) ≠ 0 := by
  simp_rw [sourceNumberFieldComplexFourier_eq]
  exact sourceComplexProductTest_actual_mellin_nonzero

theorem sourceNumberFieldComplexFourier_test_mellin_integrable :
    Integrable (fun y : {v : InfinitePlace K // IsComplex v} → ℂ =>
      sourceNumberFieldComplexFourier K sourceComplexProductTest y *
        (sourceComplexProductAbsoluteValue y ^ (1 / 6 : ℝ) /
          sourceComplexProductAbsoluteValue y : ℝ))
            (sourceComplexProductMeasure {v : InfinitePlace K // IsComplex v}) := by
  simp_rw [sourceNumberFieldComplexFourier_eq]
  exact sourceComplexProductTest_actual_mellin_integrable

end
end ArtinMatthews.VaryingKummerAnalytic
