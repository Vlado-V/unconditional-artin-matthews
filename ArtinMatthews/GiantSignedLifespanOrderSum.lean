module

public import ArtinMatthews.GiantSignedSelectedLifespanEquiv
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

/-! Removing the ordered ghost schedules cancels exactly the actual
birth factorials, on each fixed path and supported prime assignment. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

universe u

variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ)

local notation "Path" p => GiantSignedLifespanOriginalPath PS PB (ell := ell) (fun i => C i (Subtype.val (p i))) κ
local notation "Orders" => GiantSignedSelectedOrderedLifespan PS PB ell patterns C κ visitQ

theorem giantSignedSelectedOrderedLifespan_sum_birth_factor
    [∀ p : ((i : Fin n) → patterns i), Fintype (Path p)]
    (F : (p : ((i : Fin n) → patterns i)) → (path : Path p) → GiantSignedFixedLifespanChoices path visitQ → ℂ) :
    (∑ x : Orders,
      giantSignedChronologicalBirthFactor (fun i g => (giantSignedGhostVisitBorn (x.2.2.1.val g) i).card) *
        F x.1 x.2.1 x.2.2.1) =
      ∑ p : ((i : Fin n) → patterns i), ∑ path : Path p, ∑ c : GiantSignedFixedLifespanChoices path visitQ, F p path c := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro path _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  exact giantSignedLifespanBirthOrderSchedule_sum_factor c.val (F p path c)

end
end ArtinMatthews
