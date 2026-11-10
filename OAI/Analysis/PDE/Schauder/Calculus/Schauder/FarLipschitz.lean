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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.FarDerivative


set_option backward.privateInPublic true
@[expose] public section

/-! The smooth far contribution is Lipschitz at the scale r^(α−1). -/

noncomputable section
open _root_.MeasureTheory Set
namespace OAI.Analysis.PDE.Schauder

theorem farConvolution_difference_bound {m : ℕ} (hm : 1 ≤ m) (v w : EuclideanSpace ℝ (Fin m)) :
    ∃ C > 0, ∀ (r α H : ℝ), 0 < r → α < 1 → 0 ≤ H →
      ∀ (f : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 1 f → HasCompactSupport f →
      (∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) → ∀ x z,
      |scalarConvolution (truncatedNewtonianEntry m v w r) f z -
        scalarConvolution (truncatedNewtonianEntry m v w r) f x| ≤
        (H * C * (r / 2) ^ (α - 1) * rieszTailMass (volume : Measure (EuclideanSpace ℝ (Fin m))) α) * ‖z - x‖ := by
  obtain ⟨C, hC, hbound⟩ := farConvolution_fderiv_bound hm v w
  refine ⟨C, hC, ?_⟩
  intro r α H hr hα hH f hf hfc hh x z
  have hF : ContDiff ℝ 1 (scalarConvolution (truncatedNewtonianEntry m v w r) f) :=
    contDiff_scalarConvolution _ f (contDiff_truncatedNewtonianEntry m v w hr).continuous.locallyIntegrable hf hfc
  have hb (a : EuclideanSpace ℝ (Fin m)) (_ha : a ∈ (univ : Set (EuclideanSpace ℝ (Fin m)))) :
      ‖fderiv ℝ (scalarConvolution (truncatedNewtonianEntry m v w r) f) a‖ ≤
        H * C * (r / 2) ^ (α - 1) * rieszTailMass (volume : Measure (EuclideanSpace ℝ (Fin m))) α := by
    apply hbound r α H hr hα hH f hf hfc a
    intro y
    have he : a - y - a = -y := by abel
    simpa only [he, norm_neg] using hh (a - y) a
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun a _ => hF.differentiable one_ne_zero a) hb (convex_univ : Convex ℝ (univ : Set (EuclideanSpace ℝ (Fin m))))
    (mem_univ x) (mem_univ z)

end OAI.Analysis.PDE.Schauder
