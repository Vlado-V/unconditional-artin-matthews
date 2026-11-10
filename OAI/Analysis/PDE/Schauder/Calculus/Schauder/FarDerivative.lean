module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Convolution
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.TailIntegral
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.FarConvolution
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.TruncationIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! The exponent-preserving derivative estimate for the far convolution. -/

noncomputable section
open _root_.MeasureTheory
namespace OAI.Analysis.PDE.Schauder

theorem farConvolution_fderiv_bound {m : ℕ} (hm : 1 ≤ m) (v w : EuclideanSpace ℝ (Fin m)) :
    ∃ C > 0, ∀ (r α H : ℝ), 0 < r → α < 1 → 0 ≤ H →
      ∀ (f : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 1 f → HasCompactSupport f →
      ∀ x, (∀ y, |f (x - y) - f x| ≤ H * ‖y‖ ^ α) →
      ‖fderiv ℝ (scalarConvolution (truncatedNewtonianEntry m v w r) f) x‖ ≤
        H * C * (r / 2) ^ (α - 1) * rieszTailMass (volume : Measure (EuclideanSpace ℝ (Fin m))) α := by
  obtain ⟨C, hC, hbound⟩ := truncatedNewtonianEntry_weighted_fderiv v w
  refine ⟨C, hC, ?_⟩
  intro r α H hr hα hH f hf hfc x hh
  have hi0 := hbound r α volume inferInstance (by simpa using hm) hr hα
  simp only [finrank_euclideanSpace_fin] at hi0
  have hT := rieszTailMass_nonneg (volume : Measure (EuclideanSpace ℝ (Fin m))) α
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [fderiv_farConvolution_compensated hm v w hr f hf hfc x u]
  have hb : ∀ y, ‖fderiv ℝ (truncatedNewtonianEntry m v w r) y u * (f (x - y) - f x)‖ ≤
      (H * ‖u‖) * (‖fderiv ℝ (truncatedNewtonianEntry m v w r) y‖ * ‖y‖ ^ α) := by
    intro y
    rw [norm_mul, Real.norm_eq_abs (f (x - y) - f x)]
    calc
      _ ≤ (‖fderiv ℝ (truncatedNewtonianEntry m v w r) y‖ * ‖u‖) * (H * ‖y‖ ^ α) :=
        mul_le_mul ((fderiv ℝ (truncatedNewtonianEntry m v w r) y).le_opNorm u)
          (hh y) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∫ y, (H * ‖u‖) * (‖fderiv ℝ (truncatedNewtonianEntry m v w r) y‖ * ‖y‖ ^ α) :=
      norm_integral_le_of_norm_le (hi0.1.const_mul _) (Filter.Eventually.of_forall hb)
    _ = (H * ‖u‖) * ∫ y, ‖fderiv ℝ (truncatedNewtonianEntry m v w r) y‖ * ‖y‖ ^ α :=
      integral_const_mul _ _
    _ ≤ (H * ‖u‖) * (C * (r / 2) ^ (α - 1) * rieszTailMass volume α) :=
      mul_le_mul_of_nonneg_left hi0.2 (by positivity)
    _ = _ := by ring

end OAI.Analysis.PDE.Schauder
