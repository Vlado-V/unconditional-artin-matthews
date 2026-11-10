module

public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedContinuation
public import ArtinMatthews.VaryingKummerAnalyticRayRamifiedContinuation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convex.Contractible
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

/-! Actual entire continuation of every nonprincipal finite-order even ray
character, for arbitrary number-field signature. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField Set
open scoped NumberField nonZeroDivisors Classical BigOperators
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ} [NeZero N]
variable (ψ : EvenRayCharacter K N)

def nonprincipalContinued : ℂ → ℂ :=
  if hres : ψ.residue = 1 then ψ.unramifiedContinued hres else ψ.ramifiedContinued

theorem nonprincipalContinued_entire : Differentiable ℂ ψ.nonprincipalContinued := by
  unfold nonprincipalContinued
  split_ifs with hres
  · exact ψ.unramifiedContinued_entire hres
  · exact ψ.ramifiedContinued_entire hres

/-- The actual coprime-ideal witness supplies nonprincipality in the
residue-one branch; the nontrivial-residue branch has its direct theta proof. -/
theorem nonprincipalContinued_eq_dirichlet (hnp : ψ.IsNonprincipal)
    {s : ℂ} (hs : 1 < s.re) : ψ.nonprincipalContinued s = ψ.dirichlet s := by
  unfold nonprincipalContinued
  split_ifs with hres
  · exact ψ.unramifiedContinued_eq_dirichlet hres hnp hs
  · exact ψ.ramifiedContinued_eq_dirichlet hres hs

theorem nonprincipalContinued_ne_zero_right (hnp : ψ.IsNonprincipal)
    {s : ℂ} (hs : 1 < s.re) : ψ.nonprincipalContinued s ≠ 0 := by
  rw [ψ.nonprincipalContinued_eq_dirichlet hnp hs]
  exact ψ.dirichlet_ne_zero hs

theorem nonprincipalContinued_ne_zero (hnp : ψ.IsNonprincipal) :
    ψ.nonprincipalContinued ≠ 0 := by
  intro he
  exact ψ.nonprincipalContinued_ne_zero_right hnp (s := 2) (by norm_num) (congrFun he 2)

theorem nonprincipalContinued_finite_nonnegative_order (hnp : ψ.IsNonprincipal) (β : ℂ) :
    ∃ m : ℕ, meromorphicOrderAt ψ.nonprincipalContinued β = (m : WithTop ℤ) := by
  have ha : ∀ z, AnalyticAt ℂ ψ.nonprincipalContinued z :=
    fun z => ψ.nonprincipalContinued_entire.analyticAt z
  have hfin : analyticOrderAt ψ.nonprincipalContinued β ≠ ⊤ := by
    intro H
    exact ψ.nonprincipalContinued_ne_zero hnp
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero β ha).mp H)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨m, ?_⟩
  rw [(ha β).meromorphicOrderAt_eq, ← hm, ENat.map_natCast]
  rfl

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
