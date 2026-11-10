module

public import ArtinMatthews.SourceArchSphericalSection
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Instances.Matrix
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
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

theorem sourceArchMatrixEntry_continuous (i j : Fin 2) :
    Continuous (fun g : GL (Fin 2) ℂ => g i j) :=
  (_root_.continuous_apply j).comp (GeneralLinearGroup.continuous_apply id continuous_id i)

theorem sourceArchBottomNorm_continuous : Continuous sourceArchBottomNorm :=
  ((sourceArchMatrixEntry_continuous 1 0).norm.pow 2).add
    ((sourceArchMatrixEntry_continuous 1 1).norm.pow 2)

theorem sourceArchDetNorm_continuous :
    Continuous (fun g : GL (Fin 2) ℂ => ‖(GeneralLinearGroup.det g : ℂ)‖) := by
  simpa only [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Pi.mul_apply, Pi.sub_apply] using
    (((sourceArchMatrixEntry_continuous 0 0).mul (sourceArchMatrixEntry_continuous 1 1)).sub
      ((sourceArchMatrixEntry_continuous 0 1).mul (sourceArchMatrixEntry_continuous 1 0))).norm

theorem sourceArchHeight_continuous : Continuous sourceArchHeight :=
  sourceArchDetNorm_continuous.div sourceArchBottomNorm_continuous
    (fun g => (sourceArchBottomNorm_pos g).ne')

theorem sourceArchSphericalGL_continuous (s : ℂ) : Continuous (sourceArchSphericalGL s) := by
  have he : sourceArchSphericalGL s = fun g : GL (Fin 2) ℂ =>
      Complex.exp ((Real.log (sourceArchHeight g) : ℂ) * (2*s+1)) := by
    funext g
    rw [sourceArchSphericalGL, Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (sourceArchHeight_pos g).ne'),
      ← Complex.ofReal_log (sourceArchHeight_pos g).le]
  rw [he]
  exact Complex.continuous_exp.comp
    (((Complex.continuous_ofReal.comp (sourceArchHeight_continuous.log
      (fun g => (sourceArchHeight_pos g).ne'))).mul continuous_const))

end
end ArtinMatthews.SourceArchJacquet
