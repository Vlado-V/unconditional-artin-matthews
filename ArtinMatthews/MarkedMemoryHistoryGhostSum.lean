module

public import ArtinMatthews.MarkedMemoryHistoryGhostChoice
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact bundled-choice reindexing for arbitrary finite ghost summands,
including signed weights and positive Schur majorants. -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedMemoryGhostChoice_sum_deletion {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    {T : Type*} [AddCommMonoid T]
    (f : (del : MarkedRawGhostDeletion s.2.2) → (l : MarkedRawGhostBirthSizes s.2.2 del) →
      MarkedRawGhostBirthLabels l → T) :
    (∑ choice : MarkedMemoryGhostChoice hZ s, f choice.deletion choice.sizes choice.births) =
      ∑ del : MarkedRawGhostDeletion s.2.2,
        if MarkedRawGhostDeletionAllowed s.2.2 s.1.1 (hZ _ s.1.2) del then
          ∑ l : MarkedRawGhostBirthSizes s.2.2 del, ∑ births : MarkedRawGhostBirthLabels l, f del l births
        else 0 := by
  classical
  rw [← Equiv.sum_comp (markedMemoryGhostChoiceEquiv hZ s).symm]
  simp only [Fintype.sum_sigma,markedMemoryGhostChoiceEquiv,Equiv.coe_fn_symm_mk]
  let g (del : MarkedRawGhostDeletion s.2.2) :=
    ∑ l : MarkedRawGhostBirthSizes s.2.2 del, ∑ births : MarkedRawGhostBirthLabels l, f del l births
  let allowed := MarkedRawGhostDeletionAllowed s.2.2 s.1.1 (hZ _ s.1.2)
  change (∑ del : {d // allowed d},g del.1)=∑ del,if allowed del then g del else 0
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter allowed) (by simp) g).symm

end ArtinMatthews
