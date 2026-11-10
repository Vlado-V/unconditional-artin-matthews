module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
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

/-! Literal finite index partitions for unordered ghost deletion batches.
The selected and surviving tuples retain their original increasing order,
including repeated actual prime-and-anchor values. -/
namespace ArtinMatthews
open scoped BigOperators

/-- The finite-set complement has exactly the logical nonmembership type. -/
def markedRawFinsetComplEquiv {k : ℕ} (S : Finset (Fin k)) :
    ↥(Sᶜ) ≃ {i : Fin k // i ∉ S} where
  toFun i := ⟨i.1,Finset.mem_compl.mp i.2⟩
  invFun i := ⟨i.1,Finset.mem_compl.mpr i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Actual selected and surviving old indices form an exact disjoint
partition of the original indexed particle list. -/
def markedRawSubsetIndexEquiv {k : ℕ} (S : Finset (Fin k)) :
    Fin S.card ⊕ Fin (Sᶜ).card ≃ Fin k :=
  (Equiv.sumCongr (S.orderIsoOfFin rfl).toEquiv
    (((Sᶜ).orderIsoOfFin rfl).toEquiv.trans (markedRawFinsetComplEquiv S))).trans
    (Equiv.sumCompl (fun i : Fin k => i ∈ S))

/-- The actual old tuple is equivalently its indexed deleted tuple and its
indexed survivor tuple. This equivalence acts on indices, not values. -/
def markedRawSubsetTupleEquiv {X : Type*} {k : ℕ} (S : Finset (Fin k)) :
    (Fin k → X) ≃ ((Fin S.card → X) × (Fin (Sᶜ).card → X)) :=
  (Equiv.piCongrLeft' (fun _ : Fin k => X)
    (markedRawSubsetIndexEquiv S).symm).trans (Equiv.sumArrowEquivProdArrow _ _ _)

theorem markedRawSubsetTupleEquiv_deleted {X : Type*} {k : ℕ} (S : Finset (Fin k))
    (a : Fin k → X) (i : Fin S.card) :
    (markedRawSubsetTupleEquiv S a).1 i=a (S.orderEmbOfFin rfl i) := rfl

theorem markedRawSubsetTupleEquiv_survivor {X : Type*} {k : ℕ} (S : Finset (Fin k))
    (a : Fin k → X) (i : Fin (Sᶜ).card) :
    (markedRawSubsetTupleEquiv S a).2 i=a ((Sᶜ).orderEmbOfFin rfl i) := rfl

/-- Genuine product integration factors over the exact old-index partition,
with no restriction on particle-value repetitions. -/
theorem markedRawSubsetTupleEquiv_mass {X : Type*} {k : ℕ} (S : Finset (Fin k))
    (μ : X → ℂ) (a : Fin k → X) :
    (∏ i, μ (a i))=(∏ i, μ ((markedRawSubsetTupleEquiv S a).1 i))*
      ∏ i, μ ((markedRawSubsetTupleEquiv S a).2 i) := by
  classical
  have hs := Equiv.prod_comp (S.orderIsoOfFin rfl).toEquiv (fun i : S => μ (a i.1))
  have hc := Equiv.prod_comp ((Sᶜ).orderIsoOfFin rfl).toEquiv (fun i : ↥(Sᶜ) => μ (a i.1))
  change (∏ i : Fin S.card, μ (a (S.orderEmbOfFin rfl i)))=∏ i : S, μ (a i.1) at hs
  change (∏ i : Fin (Sᶜ).card, μ (a ((Sᶜ).orderEmbOfFin rfl i)))=∏ i : ↥(Sᶜ), μ (a i.1) at hc
  have hs' := hs.trans (Finset.prod_coe_sort S (fun i => μ (a i)))
  have hc' := hc.trans (Finset.prod_coe_sort (Sᶜ) (fun i => μ (a i)))
  simp only [markedRawSubsetTupleEquiv_deleted,markedRawSubsetTupleEquiv_survivor]
  rw [hs',hc']
  exact (Finset.prod_mul_prod_compl S (fun i => μ (a i))).symm

end ArtinMatthews
