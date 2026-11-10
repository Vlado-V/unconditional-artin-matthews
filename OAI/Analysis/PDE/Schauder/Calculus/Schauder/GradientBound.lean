module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine lower-order interpolation bound using the real mean-value theorem. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

theorem gradient_bound_of_function_hessian_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (hu : ContDiff ℝ 2 u) {U K : ℝ} (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hub : ∀ x, |u x| ≤ U) (hKb : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ K) :
    ∀ x, ‖fderiv ℝ u x‖ ≤ 2 * U + K := by
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ u) := (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hLip (x y : E) : ‖fderiv ℝ u y - fderiv ℝ u x‖ ≤ K * ‖y - x‖ :=
    (convex_univ : Convex ℝ (Set.univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hD x) (fun x _ => hKb x) (mem_univ x) (mem_univ y)
  intro x
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let g : E → ℝ := fun y => u y - fderiv ℝ u x y
  have hg : Differentiable ℝ g := hu1.sub (fderiv ℝ u x).differentiable
  have hgd (y : E) : fderiv ℝ g y = fderiv ℝ u y - fderiv ℝ u x := by
    exact ((hu1 y).hasFDerivAt.sub (fderiv ℝ u x).hasFDerivAt).fderiv
  have hgb (y : E) (hy : y ∈ closedBall x 1) : ‖fderiv ℝ g y‖ ≤ K := by
    rw [hgd]
    have hn : ‖y - x‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hy
    exact (hLip x y).trans (by nlinarith)
  have hx : x ∈ closedBall x 1 := mem_closedBall_self (by norm_num)
  have hxv : x + v ∈ closedBall x 1 := by
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hv, le_refl]
  have hm := (convex_closedBall x (1 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hg y) hgb hx hxv
  have he : g (x + v) - g x = (u (x + v) - u x) - fderiv ℝ u x v := by
    dsimp [g]
    rw [map_add]
    ring
  rw [he, add_sub_cancel_left, hv, mul_one, Real.norm_eq_abs] at hm
  have hd : |u (x + v) - u x| ≤ 2 * U := (abs_sub _ _).trans (by linarith [hub (x + v), hub x])
  rw [Real.norm_eq_abs]
  have := abs_sub (u (x + v) - u x) ((u (x + v) - u x) - fderiv ℝ u x v)
  rw [sub_sub_cancel] at this
  linarith

end OAI.Analysis.PDE.Schauder
