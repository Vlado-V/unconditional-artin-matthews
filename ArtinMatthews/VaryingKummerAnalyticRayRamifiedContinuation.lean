module

public import ArtinMatthews.VaryingKummerAnalyticMixedResidueContinuation
public import ArtinMatthews.VaryingKummerAnalyticRayClassRepresentatives
public import ArtinMatthews.VaryingKummerAnalyticRayClassSeries
public import ArtinMatthews.VaryingKummerAnalyticRayEuler
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

/-! Entire continuation of the genuine ray Dirichlet series when its residue
character is nontrivial, for arbitrary number-field signature. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ} [NeZero N]
variable (ψ : EvenRayCharacter K N)

def ramifiedContinued (s : ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K),
    (ψ.idealHom (rayClassFractionalRepresentative K N c) : ℂ)⁻¹ *
      mixedResidueIdealContinued K (rayClassRepresentative K N c)
        (rayClassRepresentative_ne_bot K N c) N ψ.residue s

theorem ramifiedContinued_entire (hψ : ψ.residue ≠ 1) :
    Differentiable ℂ ψ.ramifiedContinued := by
  apply Differentiable.fun_sum
  intro c _
  exact (mixedResidueIdealContinued_entire K _ _ N
    (rayClassRepresentative_coprime K N c) ψ.residue hψ).const_mul _

theorem ramifiedContinued_eq_dirichlet (hψ : ψ.residue ≠ 1)
    {s : ℂ} (hs : 1 < s.re) : ψ.ramifiedContinued s = ψ.dirichlet s := by
  rw [ψ.dirichlet_eq_residue_class_sum hs]
  unfold ramifiedContinued
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact mixedResidueIdealContinued_eq_series K _ _ N ψ.residue hψ ψ.residue_unit hs

theorem ramifiedContinued_ne_zero_right (hψ : ψ.residue ≠ 1)
    {s : ℂ} (hs : 1 < s.re) : ψ.ramifiedContinued s ≠ 0 := by
  rw [ψ.ramifiedContinued_eq_dirichlet hψ hs]
  exact ψ.dirichlet_ne_zero hs

theorem ramifiedContinued_ne_zero (hψ : ψ.residue ≠ 1) :
    ψ.ramifiedContinued ≠ 0 := by
  intro he
  have hn := ψ.ramifiedContinued_ne_zero_right hψ (s := 2) (by norm_num)
  exact hn (congrFun he 2)

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
