module

public import ArtinMatthews.MarkedMemoryActivePathData
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

/-! The actual finite path carrier is finite by its bounded coordinate
tables. The exchange and physical-ban fields are propositions. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n : ℕ} {Z : Finset (ℤ × ℤ)}

omit [Fintype J] in
theorem markedMemoryActivePath_ext
    {a b : MarkedMemoryActivePathData P pads Z n}
    (hp : a.position=b.position) (ha : a.active=b.active)
    (hi : a.incoming=b.incoming) (ho : a.outgoing=b.outgoing) : a=b := by
  cases a
  cases b
  cases hp
  cases ha
  cases hi
  cases ho
  rfl

instance markedMemoryActivePathData_finite : Finite (MarkedMemoryActivePathData P pads Z n) := by
  let encode := fun d : MarkedMemoryActivePathData P pads Z n =>
    (d.position,d.active,d.incoming,d.outgoing)
  have he : Function.Injective encode := by
    intro a b h
    have hh : a.position=b.position ∧ a.active=b.active ∧ a.incoming=b.incoming ∧ a.outgoing=b.outgoing := by
      simpa only [encode,Prod.mk.injEq] using h
    exact markedMemoryActivePath_ext hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  exact Finite.of_injective encode he

instance markedMemoryActivePathData_fintype : Fintype (MarkedMemoryActivePathData P pads Z n) :=
  Fintype.ofFinite _

end
end ArtinMatthews
