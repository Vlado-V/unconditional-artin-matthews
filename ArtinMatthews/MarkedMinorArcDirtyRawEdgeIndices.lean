module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFresh
public import ArtinMatthews.MarkedMinorArcDirtyPromotionChoices


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite coding of actual indexed promotion patterns. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedDirtyEdgePromotedIndex {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B}
    (prom : MarkedRawEdgePromotions m) (j : markedDirtyEdgePromotedGroups prom) : Fin (m.1.1 j.1:ℕ) :=
  (prom j.1).get (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp j.2).2)

theorem markedDirtyEdgePromotedIndex_spec {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B}
    (prom : MarkedRawEdgePromotions m) (j : markedDirtyEdgePromotedGroups prom) :
    prom j.1=some (markedDirtyEdgePromotedIndex prom j) := (Option.some_get _).symm

def markedDirtyEdgePromotionCode {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B}
    (prom : MarkedRawEdgePromotions m) : Σ I : Finset J, MarkedRawPromotionTuple m I :=
  ⟨markedDirtyEdgePromotedGroups prom,markedDirtyEdgePromotedIndex prom⟩

def markedDirtyEdgePromotionDecode {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B}
    (code : Σ I : Finset J, MarkedRawPromotionTuple m I) : MarkedRawEdgePromotions m :=
  fun j => if h : j ∈ code.1 then some (code.2 ⟨j,h⟩) else none

theorem markedDirtyEdgePromotionDecode_code {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B}
    (prom : MarkedRawEdgePromotions m) : markedDirtyEdgePromotionDecode (markedDirtyEdgePromotionCode prom)=prom := by
  classical
  funext j
  by_cases hj : j ∈ markedDirtyEdgePromotedGroups prom
  · change (if h : j ∈ markedDirtyEdgePromotedGroups prom then
      some (markedDirtyEdgePromotedIndex prom ⟨j,h⟩) else none)=prom j
    rw [dite_eq_left hj]
    exact (markedDirtyEdgePromotedIndex_spec prom ⟨j,hj⟩).symm
  · change (if h : j ∈ markedDirtyEdgePromotedGroups prom then
      some (markedDirtyEdgePromotedIndex prom ⟨j,h⟩) else none)=prom j
    rw [dite_eq_right hj]
    have hp : prom j=none := by
      by_contra hn
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
    exact hp.symm

theorem markedDirtyEdgePromotionCode_injective {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B} :
    Function.Injective (markedDirtyEdgePromotionCode (m := m)) :=
  (show Function.LeftInverse markedDirtyEdgePromotionDecode markedDirtyEdgePromotionCode from
    markedDirtyEdgePromotionDecode_code).injective

def markedDirtyEdgeOtherPromotionTuple {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (jstar : J) :
    MarkedRawPromotionTuple m ((markedDirtyEdgePromotedGroups prom).erase jstar) :=
  fun j => markedDirtyEdgePromotedIndex prom ⟨j.1,(Finset.mem_erase.mp j.2).2⟩

theorem markedDirtyEdgeOtherPromotionTuple_spec {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (jstar : J)
    (j : (markedDirtyEdgePromotedGroups prom).erase jstar) :
    prom j.1=some (markedDirtyEdgeOtherPromotionTuple m prom jstar j) :=
  markedDirtyEdgePromotedIndex_spec prom ⟨j.1,(Finset.mem_erase.mp j.2).2⟩

theorem markedDirtyEdgeOtherPromotedProduct_tuple {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (fresh : MarkedRawEdgeFreshLabels prom) (jstar : J) :
    markedDirtyEdgeOtherPromotedProduct m prom fresh jstar =
      markedRawPromotionTuplePrimeProduct m ((markedDirtyEdgePromotedGroups prom).erase jstar)
        (markedDirtyEdgeOtherPromotionTuple m prom jstar) := by
  classical
  unfold markedDirtyEdgeOtherPromotedProduct markedRawPromotionTuplePrimeProduct
  rw [← Finset.prod_coe_sort ((markedDirtyEdgePromotedGroups prom).erase jstar)
    (fun j => ((markedRawEdgeTargetLast m prom fresh j).1:ℕ))]
  apply Finset.prod_congr rfl
  intro j _
  rw [markedRawEdgeTargetLast_promoted m prom fresh j.1
    (markedDirtyEdgeOtherPromotionTuple m prom jstar j) (markedDirtyEdgeOtherPromotionTuple_spec m prom jstar j)]

end ArtinMatthews
