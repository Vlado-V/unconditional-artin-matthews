module

public import ArtinMatthews.MarkedMemoryPotentialChronology
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

/-! The chronological comparison splits into an earlier actual
operation, an earlier finite group in the same operation, or an earlier
literal batch index in the same group and operation. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {M B n : ℕ}

theorem markedMemoryPotentialEarlier_iff (a b : MarkedMemoryPotentialAddress J M B n) :
    MarkedMemoryPotentialEarlier a b ↔
      markedMemoryPotentialChronologicalTime a < markedMemoryPotentialChronologicalTime b ∨
      markedMemoryPotentialChronologicalTime a=markedMemoryPotentialChronologicalTime b ∧
        (Fintype.equivFin J (markedMemoryPotentialGroup a) < Fintype.equivFin J (markedMemoryPotentialGroup b) ∨
          markedMemoryPotentialGroup a=markedMemoryPotentialGroup b ∧
            markedMemoryPotentialBatchIndex a < markedMemoryPotentialBatchIndex b) := by
  unfold MarkedMemoryPotentialEarlier markedMemoryPotentialChronologicalKey
  rw [Prod.Lex.toLex_lt_toLex,Prod.Lex.toLex_lt_toLex,(Fintype.equivFin J).injective.eq_iff]

omit [Fintype J] in
theorem markedMemoryPotentialChronologicalTime_operation (a : MarkedMemoryPotentialAddress J M B n) :
    markedMemoryPotentialChronologicalTime a=
      match markedMemoryPotentialOperation a with
      | none => 0
      | some t => t+1 := by
  rcases a with ⟨j,k⟩ | ⟨t,j,k⟩ | ⟨t,j⟩ <;>
    simp only [markedMemoryPotentialChronologicalTime,markedMemoryPotentialOperation,Nat.add_assoc]

end
end ArtinMatthews
