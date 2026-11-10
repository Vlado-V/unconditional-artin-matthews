module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.KernelScale
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.KernelDerivative


set_option backward.privateInPublic true
@[expose] public section

/-! The far-field variation bound for the genuine Newtonian Hessian kernel. -/

noncomputable section
open Metric
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem newtonianEntry_difference_bound (m : ℕ) (v w : E) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : E, x ≠ 0 → ‖y - x‖ ≤ ‖x‖ / 2 →
      |newtonianEntry m v w y - newtonianEntry m v w x| ≤
        C * (‖x‖ / 2) ^ (-(m : ℝ) - 1) * ‖y - x‖ := by
  obtain ⟨C, hC, hbound⟩ := newtonianEntry_fderiv_decay m v w
  refine ⟨C, hC, ?_⟩
  intro x y hx hxy
  have hxpos : 0 < ‖x‖ / 2 := half_pos (norm_pos_iff.mpr hx)
  have hnorm (z : E) (hz : z ∈ closedBall x (‖x‖ / 2)) : ‖x‖ / 2 ≤ ‖z‖ := by
    have ht : ‖x‖ ≤ ‖z - x‖ + ‖z‖ := by
      have h := norm_add_le (x - z) z
      rw [sub_add_cancel, norm_sub_rev] at h
      exact h
    have hd : ‖z - x‖ ≤ ‖x‖ / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hz
    linarith
  have hnz (z : E) (hz : z ∈ closedBall x (‖x‖ / 2)) : z ≠ 0 :=
    norm_pos_iff.mp (hxpos.trans_le (hnorm z hz))
  have hder (z : E) (hz : z ∈ closedBall x (‖x‖ / 2)) :
      DifferentiableAt ℝ (newtonianEntry m v w) z :=
    (contDiffAt_newtonianEntry m v w (hnz z hz)).differentiableAt (by norm_num)
  have hderbound (z : E) (hz : z ∈ closedBall x (‖x‖ / 2)) :
      ‖fderiv ℝ (newtonianEntry m v w) z‖ ≤ C * (‖x‖ / 2) ^ (-(m : ℝ) - 1) := by
    apply (hbound z (hnz z hz)).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.rpow_le_rpow_of_nonpos hxpos (hnorm z hz)
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hy : y ∈ closedBall x (‖x‖ / 2) := by
    simpa only [mem_closedBall, dist_eq_norm] using hxy
  have hi := Convex.norm_image_sub_le_of_norm_fderiv_le hder hderbound
    (convex_closedBall x (‖x‖ / 2)) (mem_closedBall_self hxpos.le) hy
  simpa only [Real.norm_eq_abs] using hi

end OAI.Analysis.PDE.Schauder
