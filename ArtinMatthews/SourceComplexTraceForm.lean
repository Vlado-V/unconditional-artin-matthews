module

public import ArtinMatthews.SourceComplexProductFourier
public import OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
variable {ι : Type*} [Fintype ι]

def sourceComplexTraceForm : LinearMap.BilinForm ℝ (ι → ℂ) :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i, 2 * (x i * y i).re)
    (by intro x y z; simp [add_mul, mul_add, Finset.sum_add_distrib])
    (by
      intro r x y
      simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by intro x y z; simp [mul_add, Finset.sum_add_distrib])
    (by
      intro r x y
      simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)

theorem sourceComplexTraceForm_apply (x y : ι → ℂ) :
    sourceComplexTraceForm x y = ∑ i, 2 * (x i * y i).re := rfl

theorem sourceComplexTraceForm_symmetric (x y : ι → ℂ) :
    sourceComplexTraceForm x y = sourceComplexTraceForm y x := by
  simp only [sourceComplexTraceForm_apply, mul_comm]

theorem sourceComplexTraceForm_separating :
    (sourceComplexTraceForm (ι := ι)).SeparatingLeft := by
  intro x hx
  funext i
  have hi := hx (Pi.single i (star (x i)))
  have heq : sourceComplexTraceForm x (Pi.single i (star (x i))) = 2 * ‖x i‖ ^ 2 := by
    rw [sourceComplexTraceForm_apply, Finset.sum_eq_single i]
    · simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    · intro j _ hji
      simp [hji]
    · simp
  rw [heq] at hi
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (x i)])

instance sourceComplexTraceMeasure_isAddHaar : sourceComplexTraceMeasure.IsAddHaarMeasure := by
  change ((2 : ENNReal) • (volume : Measure ℂ)).IsAddHaarMeasure
  exact Measure.IsAddHaarMeasure.smul volume (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤)

instance sourceComplexProductMeasure_isAddHaar :
    (sourceComplexProductMeasure ι).IsAddHaarMeasure := by
  unfold sourceComplexProductMeasure
  infer_instance

theorem sourceComplexProductFourier_eq_realBilinear (f : (ι → ℂ) → ℂ) (y : ι → ℂ) :
    sourceComplexProductFourier f y =
      OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson.LocalAnalysis.realBilinearFourier
        sourceComplexTraceForm (sourceComplexProductMeasure ι) f y := by
  unfold sourceComplexProductFourier
    OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson.LocalAnalysis.realBilinearFourier
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [sourceComplexTraceForm_symmetric, sourceComplexTraceForm_apply, Circle.smul_def]
    simp only [OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters.LocalAnalysis.realCharacter_apply,
      Real.fourierChar_apply, mul_one, smul_eq_mul]
    push_cast
    ring

end
end ArtinMatthews.VaryingKummerAnalytic
