module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.CalculusWeakDifference
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.Analysis.PDE.Weak.Elliptic.Difference
public import OAI.Analysis.PDE.Weak.Elliptic.DifferenceBound


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory Filter
open scoped Topology
namespace OAI.Analysis.PDE.Weak

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem tendsto_differenceQuotient (φ : X → V) (hφ : Differentiable ℝ φ)
    (v x : X) {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0)) (hs0 : ∀ n, s n ≠ 0) :
    Tendsto (fun n ↦ differenceQuotient v (s n) φ x) atTop
      (𝓝 (fderiv ℝ φ x v)) := by
  have hp : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hd : HasDerivAt (fun t : ℝ ↦ φ (x + t • v)) (fderiv ℝ φ x v) 0 := by
    simpa only [zero_smul, add_zero, Function.comp_def] using!
      (hφ (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 hp
  have hs' : Tendsto s atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs, Eventually.of_forall hs0⟩
  simpa only [slope, sub_zero, zero_smul, add_zero, Function.comp_def, differenceQuotient,
    vsub_eq_sub]
    using hd.tendsto_slope.comp hs'

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

/-- Difference quotients of a smooth test converge inside their pairing
with an actual L¹ field, by domination from the bounded derivative. -/
theorem tendsto_integral_inner_differenceQuotient (μ : Measure X) (u φ : X → V)
    (hu : Integrable u μ) (hφ : ContDiff ℝ 1 φ) (v : X) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ φ x‖ ≤ M) {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hs0 : ∀ n, s n ≠ 0) :
    Tendsto (fun n ↦ ∫ x, inner ℝ (u x) (differenceQuotient v (s n) φ x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (u x) (fderiv ℝ φ x v) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖u x‖ * (M * ‖v‖))
  · intro n
    exact hu.aestronglyMeasurable.inner
      (continuous_differenceQuotient v (s n) hφ.continuous).aestronglyMeasurable
  · exact hu.norm.mul_const _
  · intro n
    apply Eventually.of_forall
    intro x
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (norm_differenceQuotient_le φ hφ v x (hs0 n) (fun t _ ↦ hM _)) (norm_nonneg _))
  · apply Eventually.of_forall
    intro x
    exact tendsto_const_nhds.inner (tendsto_differenceQuotient φ
      (hφ.differentiable one_ne_zero) v x hs hs0)

end OAI.Analysis.PDE.Weak
