module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Dirichlet.Hessian
public import OAI.LinearAlgebra.Moore.Derivative
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
public import Mathlib.Order.CompletePartialOrder
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
public import OAI.LinearAlgebra.Moore.Boundary


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem continuous_realHessian {n s : ℕ} {f : CoordinateSpace n s → ℝ}
    (hf : ContDiff ℝ 2 f) : Continuous (realHessian f) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ f)) := h1.fderiv_right (by norm_num)
  unfold realHessian
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (h2.continuous.clm_apply continuous_const).clm_apply continuous_const

theorem continuous_quaternionHessian {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {f : CoordinateSpace n s → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (quaternionHessian e f) := by
  have hH := continuous_realHessian hf
  unfold quaternionHessian OAI.Analysis.Calculus.Quaternion.hessianMap
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  apply continuous_finsetSum
  intro α _
  apply continuous_finsetSum
  intro β _
  exact (((continuous_apply (b, β)).comp ((continuous_apply (a, α)).comp hH))).smul continuous_const

theorem continuous_mooreHessian {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {f : CoordinateSpace n s → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (fun x ↦ OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian e f x)) :=
  (OAI.LinearAlgebra.Moore.continuous_mooreDet n).comp (continuous_quaternionHessian e hf)

theorem continuous_mooreAffineDifferential {X : Type*} [TopologicalSpace X]
    {n : ℕ} (A R : X → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : Continuous A) (hR : Continuous R) :
    Continuous (fun p : X × ℝ ↦ ‖OAI.LinearAlgebra.Moore.mooreDifferential n (A p.1 + p.2 • R p.1) (R p.1)‖) := by
  have hc : Continuous (fun p : X × ℝ ↦ (A p.1 + p.2 • R p.1, R p.1)) := by fun_prop
  exact ((OAI.LinearAlgebra.Moore.continuous_mooreDifferential n).comp
    (f := fun p : X × ℝ ↦ (A p.1 + p.2 • R p.1, R p.1)) hc).norm

end OAI.Analysis.PDE.Dirichlet
