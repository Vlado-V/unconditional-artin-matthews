module

public import ArtinMatthews.MarkedMinorArcRawMemoryBulkFactorial


set_option backward.privateInPublic true
@[expose] public section

/-! Simultaneous actual old-index subset coordinates in every prime group.
The transport is a genuine finite equivalence and keeps all repeated
numeric values, rather than passing to a quotient of particle tuples. -/
namespace ArtinMatthews
open scoped BigOperators

def MarkedRawGroupedTupleSymmetric {J : Type*} {X : J → Type*}
    (k : J → ℕ) (g : ((j : J) → Fin (k j) → X j) → ℂ) : Prop :=
  ∀ a (σ : (j : J) → Equiv.Perm (Fin (k j))),
    g (fun j => a j ∘ σ j)=g a

/-- Actual subset coordinates normalized to fixed deleted and surviving
degrees. Only the index-cardinality equalities are transported. -/
def markedRawSubsetFixedTupleEquiv {X : Type*} {k n d : ℕ}
    (S : Finset (Fin k)) (hd : S.card=d) (hn : (Sᶜ).card=n) :
    (Fin k → X) ≃ ((Fin d → X) × (Fin n → X)) := by
  cases hd
  cases hn
  exact markedRawSubsetTupleEquiv S

theorem markedRawSubsetFixedTupleEquiv_apply {X : Type*} {k n d : ℕ}
    (S : Finset (Fin k)) (hd : S.card=d) (hn : (Sᶜ).card=n) (a : Fin k → X) :
    markedRawSubsetFixedTupleEquiv S hd hn a=
      (markedRawDeletedTupleCast S hd a,markedRawSurvivorTupleCast S hn a) := by
  cases hd
  cases hn
  rfl

theorem markedRawSubsetFixedTupleEquiv_mass {X : Type*} {k n d : ℕ}
    (S : Finset (Fin k)) (hd : S.card=d) (hn : (Sᶜ).card=n) (μ : X → ℂ)
    (deleted : Fin d → X) (survivors : Fin n → X) :
    (∏ i,μ ((markedRawSubsetFixedTupleEquiv S hd hn).symm (deleted,survivors) i))=
      (∏ i,μ (deleted i))*(∏ i,μ (survivors i)) := by
  cases hd
  cases hn
  have h := markedRawSubsetTupleEquiv_mass S μ
    ((markedRawSubsetTupleEquiv S).symm (deleted,survivors))
  simpa only [markedRawSubsetFixedTupleEquiv,Equiv.apply_symm_apply] using h

theorem markedRawSubsetFixedTupleEquiv_inverse {X : Type*} {k n d : ℕ}
    (hk : n+d=k) (S : Finset (Fin k)) (hd : S.card=d) (hn : (Sᶜ).card=n)
    (deleted : Fin d → X) (survivors : Fin n → X) :
    (markedRawSubsetFixedTupleEquiv S hd hn).symm (deleted,survivors)=
      (fun i => Fin.addCases survivors deleted (Fin.cast hk.symm i)) ∘
        markedRawSubsetReassemblyPerm S := by
  cases hd
  cases hn
  rw [markedRawSubsetFixedTupleEquiv,markedRawSubsetTupleEquiv_inverse,
    markedRawSubsetCanonicalTuple_append S _ _ hk]

/-- Simultaneous actual deletion/survivor transport.  Group functions are
kept coupled; no product hypothesis is imposed on a pending test. -/
def markedRawGroupedSubsetEquiv {J : Type*} {X : J → Type*} {k n d : J → ℕ}
    (S : (j : J) → Finset (Fin (k j))) (hd : ∀ j,(S j).card=d j)
    (hn : ∀ j,((S j)ᶜ).card=n j) :
    ((j : J) → Fin (k j) → X j) ≃
      (((j : J) → Fin (d j) → X j) × ((j : J) → Fin (n j) → X j)) where
  toFun a := (fun j => (markedRawSubsetFixedTupleEquiv (S j) (hd j) (hn j) (a j)).1,
    fun j => (markedRawSubsetFixedTupleEquiv (S j) (hd j) (hn j) (a j)).2)
  invFun a := fun j => (markedRawSubsetFixedTupleEquiv (S j) (hd j) (hn j)).symm (a.1 j,a.2 j)
  left_inv a := by
    funext j
    exact (markedRawSubsetFixedTupleEquiv (S j) (hd j) (hn j)).symm_apply_apply (a j)
  right_inv a := by
    apply Prod.ext
    · funext j
      exact congrArg Prod.fst ((markedRawSubsetFixedTupleEquiv (S j) (hd j) (hn j)).apply_symm_apply (a.1 j,a.2 j))
    · funext j
      exact congrArg Prod.snd ((markedRawSubsetFixedTupleEquiv (S j) (hd j) (hn j)).apply_symm_apply (a.1 j,a.2 j))

/-- Finite simultaneous subset integration for arbitrary coupled symmetric
pending tests. This is the tensor step behind the true ghost adjunction. -/
theorem markedRawMemory_grouped_subset_integral {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j,Fintype (X j)] {k n d : J → ℕ}
    (hk : ∀ j,n j+d j=k j) (S : (j : J) → Finset (Fin (k j)))
    (hd : ∀ j,(S j).card=d j) (hn : ∀ j,((S j)ᶜ).card=n j)
    (μ : (j : J) → X j → ℂ)
    (g : ((j : J) → Fin (k j) → X j) → ℂ) (hg : MarkedRawGroupedTupleSymmetric k g)
    (f : ((j : J) → Fin (d j) → X j) → ((j : J) → Fin (n j) → X j) → ℂ) :
    (∑ a : (j : J) → Fin (k j) → X j, (∏ j,∏ i,μ j (a j i))*g a*
      f (fun j => markedRawDeletedTupleCast (S j) (hd j) (a j))
        (fun j => markedRawSurvivorTupleCast (S j) (hn j) (a j)))=
      ∑ deleted : (j : J) → Fin (d j) → X j,
        ∑ survivors : (j : J) → Fin (n j) → X j,
          (∏ j,∏ i,μ j (deleted j i))*(∏ j,∏ i,μ j (survivors j i))*
            g (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i))*
              f deleted survivors := by
  classical
  let E := markedRawGroupedSubsetEquiv (X := X) S hd hn
  rw [← Equiv.sum_comp E.symm,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro deleted _
  apply Finset.sum_congr rfl
  intro survivors _
  have hdE : (fun j => markedRawDeletedTupleCast (S j) (hd j) (E.symm (deleted,survivors) j))=deleted := by
    funext j
    have hj := congrArg Prod.fst
      ((markedRawSubsetFixedTupleEquiv (S j) (hd j) (hn j)).apply_symm_apply (deleted j,survivors j))
    rw [markedRawSubsetFixedTupleEquiv_apply] at hj
    exact hj
  have hnE : (fun j => markedRawSurvivorTupleCast (S j) (hn j) (E.symm (deleted,survivors) j))=survivors := by
    funext j
    have hj := congrArg Prod.snd
      ((markedRawSubsetFixedTupleEquiv (S j) (hd j) (hn j)).apply_symm_apply (deleted j,survivors j))
    rw [markedRawSubsetFixedTupleEquiv_apply] at hj
    exact hj
  have hm : (∏ j,∏ i,μ j (E.symm (deleted,survivors) j i))=
      (∏ j,∏ i,μ j (deleted j i))*(∏ j,∏ i,μ j (survivors j i)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    exact markedRawSubsetFixedTupleEquiv_mass (S j) (hd j) (hn j) (μ j) (deleted j) (survivors j)
  have hgE : g (E.symm (deleted,survivors))=
      g (fun j i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i)) := by
    have hx : E.symm (deleted,survivors)=
        fun j => (fun i => Fin.addCases (survivors j) (deleted j) (Fin.cast (hk j).symm i)) ∘
          markedRawSubsetReassemblyPerm (S j) := by
      funext j
      exact markedRawSubsetFixedTupleEquiv_inverse (hk j) (S j) (hd j) (hn j) (deleted j) (survivors j)
    rw [hx]
    exact hg _ _
  rw [hdE,hnE,hm,hgE]

end ArtinMatthews
