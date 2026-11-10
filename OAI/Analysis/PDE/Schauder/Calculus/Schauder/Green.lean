module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Regularized
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Presheaf
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PotentialDerivatives


set_option backward.privateInPublic true
@[expose] public section

/-! Twice integrating smooth kernels against compactly supported data by parts. -/

noncomputable section
open _root_.MeasureTheory
namespace OAI.Analysis.PDE.Schauder

theorem integral_mul_fderiv_compact {m : ℕ} (K f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hK : ContDiff ℝ 1 K) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (v : EuclideanSpace ℝ (Fin m)) :
    (∫ y, K y * fderiv ℝ f y v) = -∫ y, fderiv ℝ K y v * f y := by
  have hDK : Continuous (fun y => fderiv ℝ K y v) :=
    (hK.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDf : Continuous (fun y => fderiv ℝ f y v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hDK.mul hf.continuous).integrable_of_hasCompactSupport hfc.mul_left)
    ((hK.continuous.mul hDf).integrable_of_hasCompactSupport (hfc.fderiv_apply ℝ v).mul_left)
    ((hK.continuous.mul hf.continuous).integrable_of_hasCompactSupport hfc.mul_left)
    (fun y _ => hK.differentiable one_ne_zero y) (fun y _ => hf.differentiable one_ne_zero y)

theorem integral_mul_second_fderiv_compact {m : ℕ} (K f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hK : ContDiff ℝ 2 K) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (v w : EuclideanSpace ℝ (Fin m)) :
    (∫ y, K y * fderiv ℝ (fderiv ℝ f) y v w) =
      ∫ y, fderiv ℝ (fderiv ℝ K) y w v * f y := by
  have hDK : ContDiff ℝ 1 (fderiv ℝ K) := hK.fderiv_right (by norm_num)
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hKv : ContDiff ℝ 1 (fun y => fderiv ℝ K y v) := hDK.clm_apply contDiff_const
  have hfw : ContDiff ℝ 1 (fun y => fderiv ℝ f y w) := hDf.clm_apply contDiff_const
  calc
    _ = ∫ y, K y * fderiv ℝ (fun z => fderiv ℝ f z w) y v := by
      congr 1
      funext y
      rw [fderiv_apply_const _ y w v (hDf.differentiable one_ne_zero y)]
    _ = -∫ y, fderiv ℝ K y v * fderiv ℝ f y w :=
      integral_mul_fderiv_compact K _ (hK.of_le (by norm_num)) hfw (hfc.fderiv_apply ℝ w) v
    _ = ∫ y, fderiv ℝ (fun z => fderiv ℝ K z v) y w * f y := by
      rw [integral_mul_fderiv_compact _ f hKv (hf.of_le (by norm_num)) hfc w, neg_neg]
    _ = _ := by
      congr 1
      funext y
      rw [fderiv_apply_const _ y v w (hDK.differentiable one_ne_zero y)]

theorem shiftedRadialHessian_green {m : ℕ} (p : ℝ) {s : ℝ} (hs : 0 < s)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (v w : EuclideanSpace ℝ (Fin m)) :
    (∫ y, shiftedRadialPower p s y * fderiv ℝ (fderiv ℝ f) y v w) =
      ∫ y, shiftedRadialHessian p s y v w * f y := by
  rw [integral_mul_second_fderiv_compact _ f
    ((contDiff_shiftedRadialPower p hs).of_le (by norm_num)) hf hfc v w]
  congr 1
  funext y
  rw [second_fderiv_shiftedRadialPower p hs y]
  congr 1
  simp only [shiftedRadialHessian_apply, real_inner_comm w v]
  ring

end OAI.Analysis.PDE.Schauder
