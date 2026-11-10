module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.Calculus.Quaternion.CofactorSymbol
public import OAI.Analysis.PDE.Dirichlet.Hessian
public import Mathlib.Analysis.Quaternion
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual third Fréchet derivatives and the derivative of the quaternionic Hessian. -/

noncomputable section
namespace OAI.Analysis.Calculus.Quaternion

open OAI.Analysis.PDE.Dirichlet
open scoped Matrix Matrix.Norms.Elementwise

section General
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}

theorem thirdDerivative_swap12 (hf : ContDiffAt ℝ 3 f x) (u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x v u w := by
  have h := ((hf.fderiv_right (m := 2) (by norm_num)).isSymmSndFDerivAt
    (by norm_num)).eq u v
  exact congrArg (fun L => L w) h

theorem fderiv_second_apply (hf : ContDiffAt ℝ 3 f x) (u v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ f) y v w) x u =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u v w := by
  have hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply (hH.clm_apply (differentiableAt_const v))
    (differentiableAt_const w), fderiv_clm_apply hH (differentiableAt_const v)]
  simp

theorem thirdDerivative_swap23 (hf : ContDiffAt ℝ 3 f x) (u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u w v := by
  have heq : (fun y => fderiv ℝ (fderiv ℝ f) y v w) =ᶠ[nhds x]
      (fun y => fderiv ℝ (fderiv ℝ f) y w v) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact (hy.isSymmSndFDerivAt (by norm_num)).eq v w
  have h := congrArg (fun L : E →L[ℝ] F => L u) (heq.fderiv_eq (𝕜 := ℝ))
  simpa only [fderiv_second_apply hf] using h

end General

def thirdCoordinateTensor {m s : ℕ} (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s) (p : Fin m × Fin s) :
    Matrix (Fin m × Fin s) (Fin m × Fin s) ℝ := fun q r =>
  fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x
    (OAI.Analysis.PDE.Dirichlet.coordinateVector p) (OAI.Analysis.PDE.Dirichlet.coordinateVector q) (OAI.Analysis.PDE.Dirichlet.coordinateVector r)

theorem thirdCoordinateTensor_swap12 {m s : ℕ} {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ}
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s} (hf : ContDiffAt ℝ 3 f x) (p q r : Fin m × Fin s) :
    thirdCoordinateTensor f x p q r = thirdCoordinateTensor f x q p r :=
  thirdDerivative_swap12 hf _ _ _

theorem thirdCoordinateTensor_swap23 {m s : ℕ} {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ}
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s} (hf : ContDiffAt ℝ 3 f x) (p q r : Fin m × Fin s) :
    thirdCoordinateTensor f x p q r = thirdCoordinateTensor f x p r q :=
  thirdDerivative_swap23 hf _ _ _

theorem hasFDerivAt_realHessian {m s : ℕ} {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ}
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s} (hf : ContDiffAt ℝ 3 f x) :
    HasFDerivAt (OAI.Analysis.PDE.Dirichlet.realHessian f)
      (ContinuousLinearMap.pi fun q => ContinuousLinearMap.pi fun r =>
        ((fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x).flip (OAI.Analysis.PDE.Dirichlet.coordinateVector q)).flip
          (OAI.Analysis.PDE.Dirichlet.coordinateVector r)) x := by
  have hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  apply hasFDerivAt_pi.mpr
  intro q
  apply hasFDerivAt_pi.mpr
  intro r
  simpa [OAI.Analysis.PDE.Dirichlet.realHessian] using
    (hH.hasFDerivAt.clm_apply (hasFDerivAt_const (OAI.Analysis.PDE.Dirichlet.coordinateVector q) x)).clm_apply
      (hasFDerivAt_const (OAI.Analysis.PDE.Dirichlet.coordinateVector r) x)

theorem fderiv_realHessian_coordinate {m s : ℕ} {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ}
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s} (hf : ContDiffAt ℝ 3 f x) (p : Fin m × Fin s) :
    fderiv ℝ (OAI.Analysis.PDE.Dirichlet.realHessian f) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p) = thirdCoordinateTensor f x p := by
  have hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he (q r : Fin m × Fin s) :=
    (hH.clm_apply (differentiableAt_const (OAI.Analysis.PDE.Dirichlet.coordinateVector q))).clm_apply
      (differentiableAt_const (OAI.Analysis.PDE.Dirichlet.coordinateVector r))
  change (fderiv ℝ (fun y q r => fderiv ℝ (fderiv ℝ f) y
      (OAI.Analysis.PDE.Dirichlet.coordinateVector q) (OAI.Analysis.PDE.Dirichlet.coordinateVector r)) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p) :
      (Fin m × Fin s) → (Fin m × Fin s) → ℝ) =
    fun q r => fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x
      (OAI.Analysis.PDE.Dirichlet.coordinateVector p) (OAI.Analysis.PDE.Dirichlet.coordinateVector q) (OAI.Analysis.PDE.Dirichlet.coordinateVector r)
  rw [fderiv_pi (fun q => differentiableAt_pi.mpr (he q))]
  ext q r
  simp only [ContinuousLinearMap.pi_apply]
  rw [fderiv_pi (he q)]
  exact fderiv_second_apply hf _ _ _

def hessianContinuousLinearMap {m s : ℕ} (e : Fin s → Q) :
    Matrix (Fin m × Fin s) (Fin m × Fin s) ℝ →L[ℝ] Matrix (Fin m) (Fin m) Q :=
  (hessianLinearMap e).toContinuousLinearMap

theorem hasFDerivAt_quaternionHessian {m s : ℕ} (e : Fin s → Q)
    {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ} {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s}
    (hf : ContDiffAt ℝ 3 f x) :
    HasFDerivAt (OAI.Analysis.PDE.Dirichlet.quaternionHessian e f)
      ((hessianContinuousLinearMap e).comp (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.realHessian f) x)) x :=
  (hessianContinuousLinearMap e).hasFDerivAt.comp x
    (hasFDerivAt_realHessian hf).differentiableAt.hasFDerivAt

theorem fderiv_quaternionHessian_coordinate {m s : ℕ} (e : Fin s → Q)
    {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s → ℝ} {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s}
    (hf : ContDiffAt ℝ 3 f x) (p : Fin m × Fin s) :
    fderiv ℝ (OAI.Analysis.PDE.Dirichlet.quaternionHessian e f) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p) =
      hessianMap e (thirdCoordinateTensor f x p) := by
  rw [(hasFDerivAt_quaternionHessian e hf).fderiv]
  change hessianMap e (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.realHessian f) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) = _
  rw [fderiv_realHessian_coordinate hf]

end OAI.Analysis.Calculus.Quaternion
