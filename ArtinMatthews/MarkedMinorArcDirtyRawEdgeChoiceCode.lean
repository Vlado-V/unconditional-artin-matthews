module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFresh
public import ArtinMatthews.MarkedMinorArcRawSlotAverage


set_option backward.privateInPublic true
@[expose] public section

/-! Actual edge choices retain no hidden fresh labels in promoted groups,
and their finite index space is independent of source slot ordering. -/
noncomputable section
namespace ArtinMatthews

def markedDirtyRawEdgeChoiceReducedCode {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) :
    Z × ((J → Bool) × (Σ prom : MarkedRawEdgePromotions s.2.2,
      (j : markedDirtyEdgeFreshGroups prom) → ↥(P j.1))) :=
  (choice.target,(choice.store,⟨choice.promotions,markedDirtyEdgeFreshTuple s.2.2 choice.promotions choice.fresh⟩))

theorem markedDirtyRawEdgeChoiceReducedCode_injective {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) :
    Function.Injective (markedDirtyRawEdgeChoiceReducedCode hZ s) := by
  rintro ⟨ta,sa,pa,fa,hpa,hba⟩ ⟨tb,sb,pb,fb,hpb,hbb⟩ he
  change (ta,(sa,(Sigma.mk pa (markedDirtyEdgeFreshTuple s.2.2 pa fa) :
      Σ prom : MarkedRawEdgePromotions s.2.2, (j : markedDirtyEdgeFreshGroups prom) → ↥(P j.1))))=
    (tb,(sb,Sigma.mk pb (markedDirtyEdgeFreshTuple s.2.2 pb fb))) at he
  have ht := congrArg Prod.fst he
  cases ht
  have hp := congrArg Prod.snd he
  have hs := congrArg Prod.fst hp
  cases hs
  have hsig := congrArg Prod.snd hp
  have hprom := congrArg Sigma.fst hsig
  cases hprom
  have hf : markedDirtyEdgeFreshTuple s.2.2 pa fa=markedDirtyEdgeFreshTuple s.2.2 pa fb :=
    eq_of_heq (Sigma.mk.inj_iff.mp hsig).2
  have heq := markedDirtyEdgeFreshTuple_injective s.2.2 pa hf
  cases heq
  rfl

/-- Active source slot permutations preserve every literal edge-choice
coordinate and every admissibility constraint. They change actual source
labels and copied products, but do not create extra index multiplicity. -/
def markedDirtyRawEdgeChoiceSlotEquiv {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (σ : J → Equiv.Perm (Fin (pads+1))) :
    MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) ≃ MarkedRawEdgeChoice hZ s where
  toFun c := ⟨c.target,c.store,c.promotions,c.fresh,c.promotion_hits,c.memory_bound⟩
  invFun c := ⟨c.target,c.store,c.promotions,c.fresh,c.promotion_hits,c.memory_bound⟩
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl

end ArtinMatthews
