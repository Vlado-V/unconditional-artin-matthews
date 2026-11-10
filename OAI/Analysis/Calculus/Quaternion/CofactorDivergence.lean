module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.Calculus.Quaternion.DirectionalHessian
public import OAI.LinearAlgebra.Moore.Cofactor
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
public import OAI.LinearAlgebra.Moore.NullLagrangian
public import OAI.LinearAlgebra.Moore.Smooth


set_option backward.privateInPublic true
@[expose] public section

/-! The unconditional divergence identity for the actual Moore cofactor of a
quaternionic Hessian. No definiteness or nonsingularity hypothesis is used. -/

noncomputable section
namespace OAI.Analysis.Calculus.Quaternion

open OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix Matrix.Norms.Elementwise

theorem mooreCofactor_directionalHessian_divergence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {s : Type*} [Fintype s] [DecidableEq s]
    (e : s → Q) (d : Fin n × s → E) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 3 f x) (b : Fin n) :
    strongDivergence e
      (fun p => fderiv ℝ (fun y => OAI.LinearAlgebra.Moore.mooreCofactor n (directionalHessian e d f y)) x (d p))
      b = 0 := by
  apply directionalHessian_conservation e d hf (OAI.LinearAlgebra.Moore.mooreCofactor n)
  · exact (OAI.LinearAlgebra.Moore.contDiff_mooreCofactor n 1).differentiable (by norm_num) _
  · intro g
    exact OAI.LinearAlgebra.Moore.mooreCofactor_fderiv_outer_vecMul _ g

/-- Proposition (cofactor-divergence): the Moore cofactor of a `C³` real
function's quaternionic Hessian has zero strong quaternionic divergence.
The slots may be either the manuscript's three-slot or four-slot system. -/
theorem mooreCofactor_quaternionHessian_divergence
    {n s : ℕ} (e : Fin s → Q) {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s} (hf : ContDiffAt ℝ 3 f x) (b : Fin n) :
    strongDivergence e
      (fun p => fderiv ℝ (fun y => OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e f y)) x
        (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0 :=
  mooreCofactor_directionalHessian_divergence e OAI.Analysis.PDE.Dirichlet.coordinateVector hf b

end OAI.Analysis.Calculus.Quaternion
