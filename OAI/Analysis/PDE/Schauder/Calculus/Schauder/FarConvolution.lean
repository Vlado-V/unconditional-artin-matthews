module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Convolution
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Truncation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.TruncationIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Cancellation in the derivative of the smooth far-field convolution. -/

noncomputable section
open _root_.MeasureTheory
namespace OAI.Analysis.PDE.Schauder

theorem integrable_truncated_fderiv {m : ℕ} (hm : 1 ≤ m)
    (v w u : EuclideanSpace ℝ (Fin m)) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y => fderiv ℝ (truncatedNewtonianEntry m v w r) y u) := by
  obtain ⟨C, hC, hbound⟩ := truncatedNewtonianEntry_weighted_fderiv v w
  have hi : Integrable (fun y => ‖fderiv ℝ (truncatedNewtonianEntry m v w r) y‖) := by
    simpa using (hbound r 0 volume inferInstance (by simpa using hm) hr zero_lt_one).1
  have hc : Continuous (fun y => fderiv ℝ (truncatedNewtonianEntry m v w r) y u) :=
    ((contDiff_truncatedNewtonianEntry m v w hr).continuous_fderiv (by simp)).clm_apply continuous_const
  exact (hi.mul_const ‖u‖).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => (fderiv ℝ (truncatedNewtonianEntry m v w r) y).le_opNorm u)

theorem fderiv_farConvolution_compensated {m : ℕ} (hm : 1 ≤ m)
    (v w : EuclideanSpace ℝ (Fin m)) {r : ℝ} (hr : 0 < r)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x u : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (scalarConvolution (truncatedNewtonianEntry m v w r) f) x u =
      ∫ y, fderiv ℝ (truncatedNewtonianEntry m v w r) y u * (f (x - y) - f x) := by
  have hK : ContDiff ℝ 1 (truncatedNewtonianEntry m v w r) :=
    (contDiff_truncatedNewtonianEntry m v w hr).of_le (by simp)
  have hc : Continuous (fun y => fderiv ℝ (truncatedNewtonianEntry m v w r) y u) :=
    (hK.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hgc : HasCompactSupport (fun y => f (x - y)) := hfc.comp_homeomorph (Homeomorph.subLeft x)
  have hi1 : Integrable (fun y => fderiv ℝ (truncatedNewtonianEntry m v w r) y u * f (x - y)) :=
    (hc.mul (hf.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport hgc.mul_left
  have hi2 := (integrable_truncated_fderiv hm v w u hr).mul_const (f x)
  rw [fderiv_scalarConvolution_kernel _ f hK hf hfc x u]
  simp_rw [mul_sub]
  rw [integral_sub hi1 hi2, integral_mul_const, truncatedNewtonianEntry_fderiv_integral_zero m v w u hr volume,
    zero_mul, sub_zero]

end OAI.Analysis.PDE.Schauder
