module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFiniteSums
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFixedCode
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeDamping
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeLabelCode
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

/-! Exact transfer and damping factors in the fixed-pattern edge code. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem markedDirtyFixedEdgeChoice_prime_mass {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J) (choice : MarkedDirtyFixedEdgeChoice hZ s I) :
    markedRawEdgeChoicePrimeMass ν V hZ s choice.1 =
      finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1)
        (markedDirtyFixedEdgeChoiceCode hZ s I choice).2.2.2 * (∏ j ∈ I, (V j)⁻¹) := by
  rw [markedDirtyEdgeChoicePrimeMass_split,markedDirtyEdgeFreshGroups_eq_compl,choice.2]
  congr 1
  exact (Finset.prod_coe_sort (Finset.univ \ I)
    (fun j => ν j (markedRawEdgeTargetLast s.2.2 choice.1.promotions choice.1.fresh j))).symm

theorem markedDirtyFixedEdgeChoice_fresh_product {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (I : Finset J) (choice : MarkedDirtyFixedEdgeChoice hZ s I) :
    markedDirtyEdgeFreshProduct s.2.2 choice.1.promotions choice.1.fresh =
      ∏ j : ↥(Finset.univ \ I), (((markedDirtyFixedEdgeChoiceCode hZ s I choice).2.2.2 j).1:ℕ) := by
  unfold markedDirtyEdgeFreshProduct
  rw [markedDirtyEdgeFreshGroups_eq_compl,choice.2]
  exact (Finset.prod_coe_sort (Finset.univ \ I)
    (fun j => ((markedRawEdgeTargetLast s.2.2 choice.1.promotions choice.1.fresh j).1:ℕ))).symm

theorem markedDirtyFixedEdgeChoice_other_product {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (I : Finset J) (choice : MarkedDirtyFixedEdgeChoice hZ s I) (jstar : J) :
    markedDirtyEdgeOtherPromotedProduct s.2.2 choice.1.promotions choice.1.fresh jstar=
      markedRawPromotionTuplePrimeProduct s.2.2 (I.erase jstar)
        (markedDirtyPromotionTupleErase (markedDirtyFixedEdgeChoiceCode hZ s I choice).2.2.1 jstar) := by
  classical
  have he : (∏ j : I.erase jstar,
      ((s.2.2.2 j.1 (markedDirtyPromotionTupleErase (markedDirtyFixedEdgeChoiceCode hZ s I choice).2.2.1 jstar j)).1.1:ℕ)) =
      ∏ j : I.erase jstar, ((markedRawEdgeTargetLast s.2.2 choice.1.promotions choice.1.fresh j.1).1:ℕ) := by
    apply Finset.prod_congr rfl
    intro j _
    rw [markedRawEdgeTargetLast_promoted s.2.2 choice.1.promotions choice.1.fresh j.1 _
      (markedDirtyFixedPromotionTuple_spec s.2.2 choice.1.promotions I choice.2
        ⟨j.1,(Finset.mem_erase.mp j.2).2⟩)]
    rfl
  unfold markedRawPromotionTuplePrimeProduct
  rw [he,Finset.prod_coe_sort (I.erase jstar)
    (fun j => ((markedRawEdgeTargetLast s.2.2 choice.1.promotions choice.1.fresh j).1:ℕ))]
  unfold markedDirtyEdgeOtherPromotedProduct
  rw [choice.2]

theorem markedDirtyFixedEdgeChoice_outgoing_damping_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (I : Finset J) (choice : MarkedDirtyFixedEdgeChoice hZ s I) (jstar : J)
    {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    ρ^(markedRawPendingHits (markedRawEdgeTargetMemory hZ s choice.1) choice.1.target.1 (hZ _ choice.1.target.2)) ≤
      markedRawPromotionTupleDamping s.2.2 (I.erase jstar) choice.1.target.1 (hZ _ choice.1.target.2) ρ
        (fun _ => 0) (markedDirtyPromotionTupleErase (markedDirtyFixedEdgeChoiceCode hZ s I choice).2.2.1 jstar) := by
  classical
  let indices := markedDirtyPromotionTupleErase (markedDirtyFixedEdgeChoiceCode hZ s I choice).2.2.1 jstar
  have hi (j : I.erase jstar) : choice.1.promotions j.1=some (indices j) :=
    markedDirtyFixedPromotionTuple_spec s.2.2 choice.1.promotions I choice.2 ⟨j.1,(Finset.mem_erase.mp j.2).2⟩
  have hhit (j : I.erase jstar) : indices j ∈ markedRawGroupHitIndices s.2.2 j.1 choice.1.target.1 (hZ _ choice.1.target.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,choice.1.promotion_hits j.1 (indices j) (hi j)⟩
  have he : markedRawPromotionTupleDamping s.2.2 (I.erase jstar) choice.1.target.1 (hZ _ choice.1.target.2) ρ
      (fun _ => 0) indices = ∏ j : I.erase jstar,
        ρ^((markedRawPromotionRemainingHits s.2.2 j.1 choice.1.target.1 (hZ _ choice.1.target.2) (indices j)).card) := by
    unfold markedRawPromotionTupleDamping
    exact Finset.prod_congr rfl (fun j _ => by rw [ite_eq_left (hhit j),Nat.add_zero])
  rw [he]
  exact markedDirtyRawEdge_outgoing_damping_le hZ s choice.1 (I.erase jstar) indices hi hρ₀ hρ₁

end ArtinMatthews
