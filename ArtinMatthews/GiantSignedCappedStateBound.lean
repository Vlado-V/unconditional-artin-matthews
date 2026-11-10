module

public import ArtinMatthews.GiantSignedStateMemoryCutoff
public import ArtinMatthews.GiantSignedCappedStateDomain
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

/-! The retained states give a uniform bound for every projected test. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedStateMemoryCutoff_bound
    {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}
    [Fintype (GiantTwoSidedResidueState PS M)] [∀ g, ∀ p : PB g, NeZero p.val]
    (N : ℕ) (f : GiantSignedState PS PB M → ℂ) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ s, ‖giantSignedStateMemoryCutoff N f s‖ ≤ U := by
  classical
  let : Finite (GiantSignedCappedState PS PB M N) := giantSignedCappedState_finite N
  let := Fintype.ofFinite (GiantSignedCappedState PS PB M N)
  let U := ∑ s : GiantSignedCappedState PS PB M N, ‖f s.1‖
  have hU : 0 ≤ U := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨U, hU, ?_⟩
  intro s
  by_cases hs : (∑ g, s.2.2.1 g) ≤ N
  · rw [giantSignedStateMemoryCutoff_of_le N f s hs]
    exact Finset.single_le_sum (f := fun t : GiantSignedCappedState PS PB M N => ‖f t.1‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ ⟨s, hs⟩)
  · rw [giantSignedStateMemoryCutoff_of_lt N f s (lt_of_not_ge hs), norm_zero]
    exact hU

end
end ArtinMatthews
