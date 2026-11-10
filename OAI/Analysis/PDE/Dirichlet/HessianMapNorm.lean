module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Quaternion
public import OAI.Analysis.PDE.Dirichlet.Hessian
public import OAI.Analysis.PDE.Dirichlet.RigidMotion
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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


set_option backward.privateInPublic true
@[expose] public section

open scoped Matrix.Norms.Elementwise

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion

local instance hessianMatrixOperatorNorm {n s : ℕ} :
    Norm (Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ →L[ℝ] Matrix (Fin n) (Fin n) Q) :=
  ContinuousLinearMap.hasOpNorm

def hessianMatrixLinear {n s : ℕ} (e : Fin s → Q) :
    Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) Q where
  toFun := OAI.Analysis.Calculus.Quaternion.hessianMap e
  map_add' := OAI.Analysis.Calculus.Quaternion.hessianMap_add e
  map_smul' c A := OAI.Analysis.Calculus.Quaternion.hessianMap_smul e A c

def hessianMatrixCLM {n s : ℕ} (e : Fin s → Q) :
    Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ →L[ℝ] Matrix (Fin n) (Fin n) Q where
  toLinearMap := hessianMatrixLinear e
  cont := (hessianMatrixLinear e).continuous_of_finiteDimensional

def hessianMapBound {n s : ℕ} (e : Fin s → Q) : ℝ := ‖hessianMatrixCLM (n := n) e‖

theorem hessianMapBound_nonneg {n s : ℕ} (e : Fin s → Q) : 0 ≤ hessianMapBound (n := n) e :=
  ContinuousLinearMap.opNorm_nonneg _

theorem hessianMap_norm_le {n s : ℕ} (e : Fin s → Q)
    (H : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ) :
    ‖OAI.Analysis.Calculus.Quaternion.hessianMap e H‖ ≤ hessianMapBound (n := n) e * ‖H‖ :=
  (hessianMatrixCLM e).le_opNorm H

def gradientCoordinateLinear {n s : ℕ} (e : Fin s → Q) :
    CoordinateSpace n s →ₗ[ℝ] (Fin n → Q) where
  toFun := fun x ↦ OAI.Analysis.Calculus.Quaternion.gradientMap e x
  map_add' := by
    intro x y
    funext i
    simp [OAI.Analysis.Calculus.Quaternion.gradientMap, PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    funext i
    simp [OAI.Analysis.Calculus.Quaternion.gradientMap, PiLp.smul_apply, Finset.smul_sum, smul_smul]

def gradientCoordinateCLM {n s : ℕ} (e : Fin s → Q) :
    CoordinateSpace n s →L[ℝ] (Fin n → Q) where
  toLinearMap := gradientCoordinateLinear e
  cont := (gradientCoordinateLinear e).continuous_of_finiteDimensional

theorem gradientMap_norm_le {n s : ℕ} (e : Fin s → Q) (v : CoordinateSpace n s) :
    ‖OAI.Analysis.Calculus.Quaternion.gradientMap e v‖ ≤ ‖gradientCoordinateCLM (n := n) e‖ * ‖v‖ :=
  (gradientCoordinateCLM e).le_opNorm v

end OAI.Analysis.PDE.Dirichlet
