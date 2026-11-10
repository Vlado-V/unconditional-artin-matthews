module

public import ArtinMatthews.SourceArchDiagonalLog
public import ArtinMatthews.SourceKPAdelicUpper
public import OAI.NumberTheory.DirichletL.Eisenstein.Rows
public import ArtinMatthews.SourceArchGramNormalForm
public import ArtinMatthews.SourceKPAdelicTorusUpper
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Literal right-root and positive-diagonal motion in the existing
upper-half-space section. -/

namespace ArtinMatthews.SourceArchJacquet
open Matrix OAI.CubicEisenstein
open scoped MatrixGroups
noncomputable section

def sourceArchUpperPoint (z : ℂ) (y : ℝ) (hy : 0 < y) : PGL(2,ℂ) :=
  ProjGenLinGroup.mk (upperSection z y hy : GL (Fin 2) ℂ)

theorem sourceArchUpperPoint_normalized (z : ℂ) (y : ℝ) (hy : 0 < y) :
    sourceArchUpperPoint z y hy = ProjGenLinGroup.mk (sourceKPUpperMatrix ℂ z) *
      ProjGenLinGroup.mk (sourceKPDiagonalHom ℂ (Units.mk0 (y : ℂ) (Complex.ofReal_ne_zero.mpr hy.ne'))) := by
  have he := congrArg (fun g : GL (Fin 2) ℂ => ProjGenLinGroup.mk g)
    (sourceArchUpperSection_scalar z y hy)
  simpa only [map_mul,ProjGenLinGroup.mk_scalar,mul_one,← sourceKPUpperMatrix_field,
    ← sourceKPDiagonalHom_field,sourceArchUpperPoint] using he

theorem sourceArchUpperPoint_upper (z x : ℂ) (y : ℝ) (hy : 0 < y) :
    sourceArchUpperPoint z y hy * ProjGenLinGroup.mk (sourceKPUpperMatrix ℂ x) =
      sourceArchUpperPoint (z+(y : ℂ)*x) y hy := by
  rw [sourceArchUpperPoint_normalized,sourceArchUpperPoint_normalized,← map_mul,← map_mul,← map_mul]
  congr 1
  rw [mul_assoc,sourceKPDiagonalHom_upper,← mul_assoc,← sourceKPUpperMatrix_add]
  rfl

theorem sourceArchUpperPoint_diagonal (z : ℂ) (y t : ℝ) (hy : 0 < y) :
    sourceArchUpperPoint z y hy * ProjGenLinGroup.mk (sourceArchPositiveDiagonal t) =
      sourceArchUpperPoint z (y*Real.exp t) (mul_pos hy (Real.exp_pos t)) := by
  rw [sourceArchUpperPoint_normalized,sourceArchUpperPoint_normalized,sourceArchPositiveDiagonal,
    ← map_mul,← map_mul,← map_mul,mul_assoc,← map_mul]
  congr 2
  apply congrArg (sourceKPDiagonalHom ℂ)
  apply Units.ext
  change (y : ℂ)*(Real.exp t : ℂ) = ((y*Real.exp t : ℝ) : ℂ)
  exact (Complex.ofReal_mul y (Real.exp t)).symm

theorem sourceArchSpherical_upper_coordinates (s : ℂ) (g : GL (Fin 2) ℂ)
    (z x : ℂ) (y : ℝ) (hy : 0 < y) :
    sourceArchSphericalGL s ((g*(upperSection z y hy : GL (Fin 2) ℂ))*sourceKPUpperMatrix ℂ x) =
      sourceArchSphericalGL s (g*(upperSection (z+(y : ℂ)*x) y hy : GL (Fin 2) ℂ)) := by
  have he := congrArg (fun q : PGL(2,ℂ) => sourceArchSphericalSection s (ProjGenLinGroup.mk g*q))
    (sourceArchUpperPoint_upper z x y hy)
  simpa only [sourceArchUpperPoint,← map_mul,sourceArchSphericalSection_mk,mul_assoc] using he

theorem sourceArchSpherical_diagonal_coordinates (s : ℂ) (g : GL (Fin 2) ℂ)
    (z : ℂ) (y t : ℝ) (hy : 0 < y) :
    sourceArchSphericalGL s ((g*(upperSection z y hy : GL (Fin 2) ℂ))*sourceArchPositiveDiagonal t) =
      sourceArchSphericalGL s
        (g*(upperSection z (y*Real.exp t) (mul_pos hy (Real.exp_pos t)) : GL (Fin 2) ℂ)) := by
  have he := congrArg (fun q : PGL(2,ℂ) => sourceArchSphericalSection s (ProjGenLinGroup.mk g*q))
    (sourceArchUpperPoint_diagonal z y t hy)
  simpa only [sourceArchUpperPoint,← map_mul,sourceArchSphericalSection_mk,mul_assoc] using he

end
end ArtinMatthews.SourceArchJacquet
