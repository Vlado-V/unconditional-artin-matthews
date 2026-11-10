module

public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedEuler
public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedClassXi
public import Mathlib.Analysis.Meromorphic.Order
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

/-! Genuine entire continuation of residue-one nonprincipal ray series over
arbitrary number fields, retaining the actual deleted conductor Euler factors. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ} [NeZero N]
variable (ψ : EvenRayCharacter K N)

def unramifiedContinued (hψ : ψ.residue = 1) (s : ℂ) : ℂ :=
  mixedIdealClassContinued K (ψ.classCharacter hψ) s *
    badEulerCorrection (ψ.classUnitCharacter hψ) N s

theorem unramifiedContinued_entire (hψ : ψ.residue = 1) :
    Differentiable ℂ (ψ.unramifiedContinued hψ) :=
  (mixedIdealClassContinued_entire K _).mul (badEulerCorrection_entire _ N)

/-- Nonprincipality is the actual existence of a nontrivial value on a
nonzero coprime integral ideal. Values at omitted primes are not used. -/
theorem unramifiedContinued_eq_dirichlet (hψ : ψ.residue = 1) (hnp : ψ.IsNonprincipal)
    {s : ℂ} (hs : 1 < s.re) :
    ψ.unramifiedContinued hψ s = ψ.dirichlet s := by
  rw [unramifiedContinued, mixedIdealClassContinued_eq K _
    (ψ.classCharacter_ne_one_of_nonprincipal hψ hnp) hs]
  exact (ψ.dirichlet_of_residue_one hψ hs).symm

theorem unramifiedContinued_ne_zero (hψ : ψ.residue = 1) (hnp : ψ.IsNonprincipal) :
    ψ.unramifiedContinued hψ ≠ 0 := by
  intro H
  have HE := ψ.unramifiedContinued_eq_dirichlet hψ hnp (s := 2) (by norm_num)
  rw [H, Pi.zero_apply] at HE
  exact ψ.dirichlet_ne_zero (by norm_num : 1 < (2 : ℂ).re) HE.symm

theorem unramifiedContinued_finite_nonnegative_order
    (hψ : ψ.residue = 1) (hnp : ψ.IsNonprincipal) (β : ℂ) :
    ∃ m : ℕ, meromorphicOrderAt (ψ.unramifiedContinued hψ) β = (m : WithTop ℤ) := by
  have ha : ∀ z, AnalyticAt ℂ (ψ.unramifiedContinued hψ) z :=
    fun z => (ψ.unramifiedContinued_entire hψ).analyticAt z
  have hfin : analyticOrderAt (ψ.unramifiedContinued hψ) β ≠ ⊤ := by
    intro H
    exact ψ.unramifiedContinued_ne_zero hψ hnp
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero β ha).mp H)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨m, ?_⟩
  rw [(ha β).meromorphicOrderAt_eq, ← hm, ENat.map_natCast]
  rfl

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
