module

public import ArtinMatthews.MarkedMinorArcRawMemorySymmetry
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Sum


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
