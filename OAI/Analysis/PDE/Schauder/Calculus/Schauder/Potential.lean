module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Newtonian
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Newtonian convolution and its classical derivatives for smooth compact data. -/

noncomputable section
open _root_.MeasureTheory
open scoped Convolution
namespace OAI.Analysis.PDE.Schauder

theorem locallyIntegrable_newtonianKernel {m : ℕ} (hm : 1 ≤ m) :
    LocallyIntegrable (newtonianKernel (E := EuclideanSpace ℝ (Fin m)) m) := by
  apply locallyIntegrable_of_norm_le_rpow (by simpa using hm)
    (α := (m : ℝ) - 2) (C := 1) (by simp only [finrank_euclideanSpace_fin]; linarith)
  · filter_upwards [] with y
    rw [newtonianKernel_eq_norm_rpow, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _), one_mul]
    simp only [neg_sub]
    exact le_rfl
  · have he : newtonianKernel (E := EuclideanSpace ℝ (Fin m)) m =
        fun y => ‖y‖ ^ (2 - (m : ℝ)) := funext (newtonianKernel_eq_norm_rpow m)
    rw [he]
    exact (measurable_norm.pow_const _).aestronglyMeasurable

def newtonianPotential {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ y, newtonianKernel m y * f (x - y)

theorem newtonianPotential_eq_convolution {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) :
    newtonianPotential f =
      newtonianKernel m ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f := rfl

theorem newtonianPotential_integrable {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun y => newtonianKernel m y * f (x - y)) :=
  hfc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_newtonianKernel hm) hf x

theorem contDiff_newtonianPotential {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) {k : ℕ∞} (hf : ContDiff ℝ k f)
    (hfc : HasCompactSupport f) : ContDiff ℝ k (newtonianPotential f) := by
  rw [newtonianPotential_eq_convolution]
  exact hfc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_newtonianKernel hm) hf

theorem hasFDerivAt_newtonianPotential {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt (newtonianPotential f)
      ((newtonianKernel m ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR
        (EuclideanSpace ℝ (Fin m)), volume] fderiv ℝ f) x) x := by
  rw [newtonianPotential_eq_convolution]
  exact hfc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_newtonianKernel hm) hf x

end OAI.Analysis.PDE.Schauder
