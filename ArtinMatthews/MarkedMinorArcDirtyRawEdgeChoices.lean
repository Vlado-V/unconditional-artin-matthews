module

public import ArtinMatthews.MarkedMinorArcRawEdgeAction
public import ArtinMatthews.MarkedMinorArcDirtyPermutation


set_option backward.privateInPublic true
@[expose] public section

/-! Exact prime products and transfer masses of the literal RawEdge choices. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedDirtyEdgeFreshGroups {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B}
    (prom : MarkedRawEdgePromotions m) : Finset J := by
  classical
  exact Finset.univ.filter (fun j => prom j=none)

def markedDirtyEdgePromotedGroups {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B}
    (prom : MarkedRawEdgePromotions m) : Finset J := by
  classical
  exact Finset.univ.filter (fun j => prom j≠none)

def markedDirtyEdgeFreshProduct {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (fresh : MarkedRawEdgeFreshLabels prom) : ℕ :=
  ∏ j ∈ markedDirtyEdgeFreshGroups prom, ((markedRawEdgeTargetLast m prom fresh j).1:ℕ)

def markedDirtyEdgeOtherPromotedProduct {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (fresh : MarkedRawEdgeFreshLabels prom) (jstar : J) : ℕ :=
  ∏ j ∈ (markedDirtyEdgePromotedGroups prom).erase jstar, ((markedRawEdgeTargetLast m prom fresh j).1:ℕ)

theorem markedDirtyEdgeTargetProduct_split {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (fresh : MarkedRawEdgeFreshLabels prom)
    (jstar : J) (kstar : Fin (m.1.1 jstar:ℕ)) (hk : prom jstar=some kstar) :
    markedRawLastProduct (markedRawEdgeTargetLast m prom fresh)=
      ((m.2 jstar kstar).1.1:ℕ)*markedDirtyEdgeOtherPromotedProduct m prom fresh jstar*
        markedDirtyEdgeFreshProduct m prom fresh := by
  classical
  have hj : jstar ∈ markedDirtyEdgePromotedGroups prom := by
    simp [markedDirtyEdgePromotedGroups,hk]
  have hp := Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => prom j=none)
    (fun j => ((markedRawEdgeTargetLast m prom fresh j).1:ℕ))
  have he := Finset.mul_prod_erase (markedDirtyEdgePromotedGroups prom)
    (fun j => ((markedRawEdgeTargetLast m prom fresh j).1:ℕ)) hj
  change ((markedRawEdgeTargetLast m prom fresh jstar).1:ℕ)*
      markedDirtyEdgeOtherPromotedProduct m prom fresh jstar=
      ∏ j ∈ markedDirtyEdgePromotedGroups prom, ((markedRawEdgeTargetLast m prom fresh j).1:ℕ) at he
  rw [markedRawEdgeTargetLast_promoted m prom fresh jstar kstar hk] at he
  change markedDirtyEdgeFreshProduct m prom fresh *
      (∏ j ∈ markedDirtyEdgePromotedGroups prom, ((markedRawEdgeTargetLast m prom fresh j).1:ℕ))=
      markedRawLastProduct (markedRawEdgeTargetLast m prom fresh) at hp
  rw [← he] at hp
  exact hp.symm.trans (by ring)

theorem markedDirtyEdgeTargetLast_none {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (fresh : MarkedRawEdgeFreshLabels prom) (j : J)
    (hp : prom j=none) : markedRawEdgeTargetLast m prom fresh j=(by simpa only [hp] using fresh j) := by
  unfold markedRawEdgeTargetLast
  split
  · rfl
  · rename_i k hs
    rw [hp] at hs
    cases hs

theorem markedDirtyEdgeChoicePrimeMass_split {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoicePrimeMass ν V hZ s choice=
      (∏ j ∈ markedDirtyEdgeFreshGroups choice.promotions,
        ν j (markedRawEdgeTargetLast s.2.2 choice.promotions choice.fresh j))*
      (∏ j ∈ markedDirtyEdgePromotedGroups choice.promotions, (V j)⁻¹) := by
  classical
  unfold markedRawEdgeChoicePrimeMass markedDirtyEdgeFreshGroups markedDirtyEdgePromotedGroups
  rw [Finset.prod_filter,Finset.prod_filter,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  split
  · rename_i hp
    simp only [hp,ite_true,ne_self_iff_false,ite_false,mul_one]
    rw [markedDirtyEdgeTargetLast_none s.2.2 choice.promotions choice.fresh j hp]
  · rename_i k hp
    simp [hp]

theorem markedDirtyEdgeCrossBan_prime_ne {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M : ℕ} (source : MarkedRawActive P M)
    (target : (j : J) → ↥(P j)) (hban : ¬MarkedRawFullCrossBan source target) :
    ∀ j k i, (source j k).1 ≠ (target i).1 := by
  intro j k i he
  exact hban ⟨i,j,k,he.symm⟩

/-- Actual source-ban separation for the other promoted product. -/
theorem markedDirtyEdgeCrossBan_other_coprime {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (m : MarkedRawMemory P B) (prom : MarkedRawEdgePromotions m)
    (fresh : MarkedRawEdgeFreshLabels prom) (jstar : J)
    (hban : ¬MarkedRawFullCrossBan source (markedRawEdgeTargetLast m prom fresh)) :
    (markedSourceFullProduct (markedRawNumericActive source)).Coprime
      (markedDirtyEdgeOtherPromotedProduct m prom fresh jstar) := by
  have hc := markedSourceFull_coprime_promoted_of_cross_ban
    (markedRawNumericActive source) (fun j k => (source j k).1.2)
    (fun i : (markedDirtyEdgePromotedGroups prom).erase jstar =>
      ((markedRawEdgeTargetLast m prom fresh i.1).1:ℕ))
    (fun i => (markedRawEdgeTargetLast m prom fresh i.1).1.2)
    (fun j k i he => markedDirtyEdgeCrossBan_prime_ne source _ hban j k i.1 (Subtype.ext he))
  have he : (∏ i : (markedDirtyEdgePromotedGroups prom).erase jstar,
      ((markedRawEdgeTargetLast m prom fresh i.1).1:ℕ)) =
      markedDirtyEdgeOtherPromotedProduct m prom fresh jstar :=
    Finset.prod_coe_sort _ (fun j => ((markedRawEdgeTargetLast m prom fresh j).1:ℕ))
  rwa [he] at hc

end ArtinMatthews
