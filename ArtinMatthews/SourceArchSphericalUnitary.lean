module

public import ArtinMatthews.SourceArchSphericalSection
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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

/-! Right invariance of the actual spherical section under the
unitary matrix subgroup. The bottom-row norm is its Gram diagonal. -/
namespace ArtinMatthews.SourceArchJacquet

open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

def sourceArchUnitaryGL : Matrix.unitaryGroup (Fin 2) ℂ →* GL (Fin 2) ℂ :=
  Unitary.toUnits

def sourceArchUnitaryPGL : Matrix.unitaryGroup (Fin 2) ℂ →* PGL(2, ℂ) :=
  ProjGenLinGroup.mk.comp sourceArchUnitaryGL

theorem sourceArchBottomNorm_gram (g : GL (Fin 2) ℂ) :
    ((sourceArchBottomNorm g : ℝ) : ℂ) =
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ)) 1 1 := by
  simp [sourceArchBottomNorm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Complex.mul_conj']

theorem sourceArchBottomNorm_unitary (g : GL (Fin 2) ℂ) (k : Matrix.unitaryGroup (Fin 2) ℂ) :
    sourceArchBottomNorm (g * sourceArchUnitaryGL k) = sourceArchBottomNorm g := by
  apply Complex.ofReal_injective
  rw [sourceArchBottomNorm_gram, sourceArchBottomNorm_gram]
  have hk : (k : Matrix (Fin 2) (Fin 2) ℂ) * star (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    k.property.2
  change (((g : Matrix (Fin 2) (Fin 2) ℂ) * k.val) * star ((g : Matrix (Fin 2) (Fin 2) ℂ) * k.val)) 1 1 = _
  rw [star_mul, mul_assoc, ← mul_assoc k.val, hk, one_mul]

theorem sourceArchUnitaryGL_det_norm (k : Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖(GeneralLinearGroup.det (sourceArchUnitaryGL k) : ℂ)‖ = 1 := by
  exact CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary k.property)

theorem sourceArchHeight_unitary (g : GL (Fin 2) ℂ) (k : Matrix.unitaryGroup (Fin 2) ℂ) :
    sourceArchHeight (g * sourceArchUnitaryGL k) = sourceArchHeight g := by
  rw [sourceArchHeight, sourceArchBottomNorm_unitary, map_mul, Units.val_mul, norm_mul,
    sourceArchUnitaryGL_det_norm, mul_one]
  rfl

theorem sourceArchSphericalSection_unitary (s : ℂ) (g : PGL(2, ℂ))
    (k : Matrix.unitaryGroup (Fin 2) ℂ) :
    sourceArchSphericalSection s (g * sourceArchUnitaryPGL k) = sourceArchSphericalSection s g := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g =>
    change sourceArchSphericalSection s (ProjGenLinGroup.mk g * ProjGenLinGroup.mk (sourceArchUnitaryGL k)) = _
    rw [← map_mul, sourceArchSphericalSection_mk, sourceArchSphericalGL, sourceArchHeight_unitary,
      sourceArchSphericalSection_mk, sourceArchSphericalGL]

end
end ArtinMatthews.SourceArchJacquet
