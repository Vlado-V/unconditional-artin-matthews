module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Prime.Defs
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Strict earlier-coordinate prime values of a genuinely typed finite
prime tuple. Appending the last draw preserves all earlier prefixes. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

def markedPrimeTuplePrefix {n : ℕ} {P : Fin n → Finset Nat.Primes}
    (t : (i : Fin n) → ↥(P i)) (i : Fin n) : Fin i.val → Nat.Primes :=
  fun j => (t ⟨j.val,j.isLt.trans i.isLt⟩).1

theorem markedPrimeTuplePrefix_snoc_castSucc {n : ℕ}
    {P : Fin (n+1) → Finset Nat.Primes}
    (t : (i : Fin n) → ↥(P i.castSucc)) (p : P (Fin.last n)) (i : Fin n) :
    markedPrimeTuplePrefix (Fin.snoc t p) i.castSucc=markedPrimeTuplePrefix t i := by
  funext j
  change ((Fin.snoc (α := fun k => ↥(P k)) t p) (Fin.castSucc ⟨j.val,j.isLt.trans i.isLt⟩)).1=
    (t ⟨j.val,j.isLt.trans i.isLt⟩).1
  rw [Fin.snoc_castSucc]

theorem markedPrimeTuplePrefix_snoc_last {n : ℕ}
    {P : Fin (n+1) → Finset Nat.Primes}
    (t : (i : Fin n) → ↥(P i.castSucc)) (p : P (Fin.last n)) :
    markedPrimeTuplePrefix (Fin.snoc t p) (Fin.last n)=(fun i => (t i).1) := by
  funext i
  change ((Fin.snoc (α := fun k => ↥(P k)) t p) i.castSucc).1=(t i).1
  rw [Fin.snoc_castSucc]

end
end ArtinMatthews
