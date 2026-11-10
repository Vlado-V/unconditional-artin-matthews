module

public import ArtinMatthews.SourceComplexAdelicCharacter
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import ArtinMatthews.SourceComplexAdelicNorm
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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
open MeasureTheory NumberField NumberField.InfinitePlace
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]

def sourceNumberFieldArchProbe (a : InfiniteAdeleRing K) : ℂ :=
  sourceComplexProductTest ((InfiniteAdeleRing.ringEquiv_mixedSpace K a).2)

omit [IsTotallyComplex K] in
theorem sourceNumberFieldArchProbe_apply
    (x : {v : InfinitePlace K // IsComplex v} → ℂ) :
    sourceNumberFieldArchProbe K (sourceComplexPlaceAdele K x) = sourceComplexProductTest x := by
  change sourceComplexProductTest
    (((InfiniteAdeleRing.ringEquiv_mixedSpace K)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (0, x))).2) = _
  rw [RingEquiv.apply_symm_apply]

theorem sourceNumberFieldArchProbe_fourier_mellin_nonzero :
    (∫ y : {v : InfinitePlace K // IsComplex v} → ℂ,
      sourceNumberFieldComplexFourier K (fun x => sourceNumberFieldArchProbe K
        (sourceComplexPlaceAdele K x)) y *
        (mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace K
          (sourceComplexPlaceAdele K y)) ^ (1 / 6 : ℝ) /
        mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace K
          (sourceComplexPlaceAdele K y)) : ℝ)
            ∂sourceComplexProductMeasure {v : InfinitePlace K // IsComplex v}) ≠ 0 := by
  simp_rw [sourceNumberFieldArchProbe_apply, sourceComplexPlaceAdele_mixed_norm]
  exact sourceNumberFieldComplexFourier_test_mellin_nonzero K

theorem sourceNumberFieldArchProbe_fourier_mellin_integrable :
    Integrable (fun y : {v : InfinitePlace K // IsComplex v} → ℂ =>
      sourceNumberFieldComplexFourier K (fun x => sourceNumberFieldArchProbe K
        (sourceComplexPlaceAdele K x)) y *
        (mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace K
          (sourceComplexPlaceAdele K y)) ^ (1 / 6 : ℝ) /
        mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace K
          (sourceComplexPlaceAdele K y)) : ℝ))
            (sourceComplexProductMeasure {v : InfinitePlace K // IsComplex v}) := by
  simp_rw [sourceNumberFieldArchProbe_apply, sourceComplexPlaceAdele_mixed_norm]
  exact sourceNumberFieldComplexFourier_test_mellin_integrable K

theorem sourceNumberFieldArchProbe_fourier_zero :
    sourceNumberFieldComplexFourier K (fun x => sourceNumberFieldArchProbe K
      (sourceComplexPlaceAdele K x)) 0 = 0 := by
  simp_rw [sourceNumberFieldArchProbe_apply]
  exact sourceNumberFieldComplexFourier_test_zero K

end
end ArtinMatthews.VaryingKummerAnalytic
