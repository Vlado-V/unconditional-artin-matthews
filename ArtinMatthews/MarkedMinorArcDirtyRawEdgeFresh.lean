module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeChoices
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


set_option backward.privateInPublic true
@[expose] public section

/-! Literal fresh coordinates of a fixed actual promotion pattern. Promoted
slots have singleton fresh-label types, hence introduce no size factor. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedDirtyEdgeFreshTuple {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (fresh : MarkedRawEdgeFreshLabels prom) :
    (j : markedDirtyEdgeFreshGroups prom) → ↥(P j.1) :=
  fun j => markedRawEdgeTargetLast m prom fresh j.1

theorem markedDirtyEdgeFreshTuple_injective {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) : Function.Injective (markedDirtyEdgeFreshTuple m prom) := by
  classical
  intro a b hab
  funext j
  by_cases hp : prom j=none
  · have hj : j ∈ markedDirtyEdgeFreshGroups prom := by simp [markedDirtyEdgeFreshGroups,hp]
    have hh := congrFun hab ⟨j,hj⟩
    change markedRawEdgeTargetLast m prom a j=markedRawEdgeTargetLast m prom b j at hh
    rw [markedDirtyEdgeTargetLast_none m prom a j hp,markedDirtyEdgeTargetLast_none m prom b j hp] at hh
    let β : Option (Fin (m.1.1 j:ℕ)) → Type := fun o => match o with | none => ↥(P j) | some _ => PUnit
    exact (Equiv.cast (congrArg β hp)).injective hh
  · have hs : Subsingleton (match prom j with | none => ↥(P j) | some _ => PUnit) := by
      split
      · rename_i hn
        exact False.elim (hp hn)
      · infer_instance
    exact hs.elim _ _

theorem markedDirtyEdgeFreshProduct_tuple {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (fresh : MarkedRawEdgeFreshLabels prom) :
    markedDirtyEdgeFreshProduct m prom fresh =
      ∏ j : markedDirtyEdgeFreshGroups prom, ((markedDirtyEdgeFreshTuple m prom fresh j).1:ℕ) :=
  (Finset.prod_coe_sort _ (fun j => ((markedRawEdgeTargetLast m prom fresh j).1:ℕ))).symm

theorem markedDirtyEdgeChoicePrimeMass_fresh_tuple {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoicePrimeMass ν V hZ s choice=
      finiteProductMass (fun j : markedDirtyEdgeFreshGroups choice.promotions => ν j.1)
        (markedDirtyEdgeFreshTuple s.2.2 choice.promotions choice.fresh)*
      (∏ j ∈ markedDirtyEdgePromotedGroups choice.promotions, (V j)⁻¹) := by
  rw [markedDirtyEdgeChoicePrimeMass_split]
  congr 1
  exact (Finset.prod_coe_sort _ (fun j => ν j (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j))).symm

end ArtinMatthews
