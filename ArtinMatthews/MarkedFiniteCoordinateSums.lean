module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Pi
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

/-! Finite coordinate sums with genuine zero extension. The change of
finite carrier is constructed pointwise on the actual nonzero support. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedFiniteCoordinateSum_eq {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (G T : Finset α) (f : (ι → α) → ℂ)
    (hG : ∀ x,f x≠0 → ∀ i,x i∈G) (hT : ∀ x,f x≠0 → ∀ i,x i∈T) :
    (∑ x : ι → G,f (fun i => (x i).1))=
      ∑ x : ι → T,f (fun i => (x i).1) := by
  apply Finset.sum_bij_ne_zero
    (fun x _ hx i => (⟨(x i).1,hT (fun j => (x j).1) hx i⟩ : T))
  · intro x _ _
    exact Finset.mem_univ _
  · intro x _ _ y _ _ he
    funext i
    apply Subtype.ext
    exact congrArg (fun a => (a i).1) he
  · intro y _ hy
    let x : ι → G := fun i => ⟨(y i).1,hG (fun j => (y j).1) hy i⟩
    exact ⟨x,Finset.mem_univ _,hy,rfl⟩
  · intro x _ _
    rfl

end
end ArtinMatthews
