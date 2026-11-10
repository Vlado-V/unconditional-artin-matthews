module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.CoefficientExtension
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded
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


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

theorem ellipticExtension_smoothBounded {m : ℕ}
    {A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m}
    {θ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hA : ContDiff ℝ ∞ A) (hθ : ContDiff ℝ ∞ θ) (hs : HasCompactSupport θ)
    (lam : ℝ) : SmoothBounded (ellipticExtension A θ lam) := by
  let : NormedAddCommGroup (OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) :=
    ContinuousLinearMap.toNormedSpace
  let C := lam • ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Variational.CellVectors m)
  let B : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m := fun x ↦ θ x • (A x - C)
  have hB : ContDiff ℝ ∞ B := hθ.smul (hA.sub contDiff_const)
  have hBs : HasCompactSupport B := hs.smul_right
  have heq : ellipticExtension A θ lam = (fun _ : OAI.Analysis.PDE.Variational.CellCoordinates m ↦ C) + B := by
    funext x
    change θ x • A x + (1 - θ x) • (lam • ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Variational.CellVectors m)) =
      C + θ x • (A x - C)
    change θ x • A x + (1 - θ x) • C = C + θ x • (A x - C)
    rw [sub_smul, one_smul, smul_sub]
    abel
  rw [heq]
  exact (smoothBounded_const (m := m) C).add (smoothBounded_of_hasCompactSupport hB hBs)

end OAI.Analysis.PDE.Weak
