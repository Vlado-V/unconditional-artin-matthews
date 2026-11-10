module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Quaternion
public import OAI.Analysis.Calculus.Quaternion.CofactorSymbol
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import OAI.Analysis.Calculus.Quaternion.ThirdDerivatives


set_option backward.privateInPublic true
@[expose] public section

/-! Hessian conservation along arbitrary fixed real directions. -/

noncomputable section
namespace OAI.Analysis.Calculus.Quaternion

open scoped Matrix Matrix.Norms.Elementwise

variable {E m s : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype m] [Fintype s] [DecidableEq m] [DecidableEq s]

def directionalRealHessian (d : m × s → E) (f : E → ℝ) (x : E) :
    Matrix (m × s) (m × s) ℝ :=
  fun p q => fderiv ℝ (fderiv ℝ f) x (d p) (d q)

def directionalHessian (e : s → Q) (d : m × s → E) (f : E → ℝ) (x : E) :
    Matrix m m Q := hessianMap e (directionalRealHessian d f x)

def directionalThirdTensor (d : m × s → E) (f : E → ℝ) (x : E)
    (p : m × s) : Matrix (m × s) (m × s) ℝ :=
  fun q r => fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x (d p) (d q) (d r)

omit [DecidableEq m] [DecidableEq s] in
theorem hasFDerivAt_directionalRealHessian (d : m × s → E)
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 f x) :
    HasFDerivAt (directionalRealHessian d f)
      (ContinuousLinearMap.pi fun q => ContinuousLinearMap.pi fun r =>
        ((fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x).flip (d q)).flip (d r)) x := by
  have hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  apply hasFDerivAt_pi.mpr
  intro q
  apply hasFDerivAt_pi.mpr
  intro r
  simpa [directionalRealHessian] using!
    (hH.hasFDerivAt.clm_apply (hasFDerivAt_const (d q) x)).clm_apply
      (hasFDerivAt_const (d r) x)

omit [DecidableEq m] [DecidableEq s] in
theorem fderiv_directionalRealHessian (d : m × s → E)
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 f x) (p : m × s) :
    fderiv ℝ (directionalRealHessian d f) x (d p) = directionalThirdTensor d f x p := by
  have hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he (q r : m × s) :=
    (hH.clm_apply (differentiableAt_const (d q))).clm_apply (differentiableAt_const (d r))
  change (fderiv ℝ (fun y q r => fderiv ℝ (fderiv ℝ f) y (d q) (d r)) x (d p) :
      (m × s) → (m × s) → ℝ) =
    fun q r => fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x (d p) (d q) (d r)
  rw [fderiv_pi (fun q => differentiableAt_pi.mpr (he q))]
  ext q r
  simp only [ContinuousLinearMap.pi_apply]
  rw [fderiv_pi (he q)]
  exact fderiv_second_apply hf _ _ _

def hessianCLM (e : s → Q) :
    Matrix (m × s) (m × s) ℝ →L[ℝ] Matrix m m Q :=
  (hessianLinearMap e).toContinuousLinearMap

omit [DecidableEq m] [DecidableEq s] in
theorem hasFDerivAt_directionalHessian (e : s → Q) (d : m × s → E)
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 f x) :
    HasFDerivAt (directionalHessian e d f)
      ((hessianCLM e).comp (fderiv ℝ (directionalRealHessian d f) x)) x := by
  simpa only using! (hessianCLM e).hasFDerivAt.comp x
    (hasFDerivAt_directionalRealHessian d hf).differentiableAt.hasFDerivAt

omit [DecidableEq m] [DecidableEq s] in
theorem fderiv_directionalHessian (e : s → Q) (d : m × s → E)
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 f x) (p : m × s) :
    fderiv ℝ (directionalHessian e d f) x (d p) =
      hessianMap e (directionalThirdTensor d f x p) := by
  have hF : fderiv ℝ (directionalHessian e d f) x =
      (hessianCLM e).comp (fderiv ℝ (directionalRealHessian d f) x) := by
    simpa only using! (hasFDerivAt_directionalHessian e d hf).fderiv
  rw [hF]
  change hessianMap e (fderiv ℝ (directionalRealHessian d f) x (d p)) = _
  rw [fderiv_directionalRealHessian d hf]

/-- Conservation for a differentiable matrix function whose linearized cubic
symbol vanishes. This lemma is specialized to the actual Moore cofactor below. -/
theorem directionalHessian_conservation (e : s → Q) (d : m × s → E)
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 f x)
    (C : Matrix m m Q → Matrix m m Q)
    (hC : DifferentiableAt ℝ C (directionalHessian e d f x))
    (hnull : ∀ g : m → Q,
      star g ᵥ* (fderiv ℝ C (directionalHessian e d f x) (outer g)) = 0) (b : m) :
    strongDivergence e
      (fun p => fderiv ℝ (fun y => C (directionalHessian e d f y)) x (d p)) b = 0 := by
  have hd (p : m × s) :
      fderiv ℝ (fun y => C (directionalHessian e d f y)) x (d p) =
        fderiv ℝ C (directionalHessian e d f x)
          (hessianMap e (directionalThirdTensor d f x p)) := by
    have hF : fderiv ℝ (fun y => C (directionalHessian e d f y)) x =
        (fderiv ℝ C (directionalHessian e d f x)).comp
          (fderiv ℝ (directionalHessian e d f) x) := by
      simpa only [Function.comp_def] using!
        fderiv_comp x hC (hasFDerivAt_directionalHessian e d hf).differentiableAt
    rw [hF]
    simp only [ContinuousLinearMap.comp_apply, fderiv_directionalHessian e d hf]
  simp only [hd]
  apply hessian_cofactor_symbol_zero e (fderiv ℝ C (directionalHessian e d f x)).toLinearMap
    hnull (directionalThirdTensor d f x)
  · intro p q r
    exact thirdDerivative_swap12 hf _ _ _
  · intro p q r
    exact thirdDerivative_swap23 hf _ _ _

end OAI.Analysis.Calculus.Quaternion
