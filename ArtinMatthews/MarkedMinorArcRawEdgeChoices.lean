module

public import ArtinMatthews.MarkedMinorArcRawEdgeState
public import ArtinMatthews.MarkedMinorArcRawGhostIdentity


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite edge-choice indexing, including the exact no-store and
no-promotion branch used by the already proved raw clean operator. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Erase only the admissibility proofs; every literal edge choice remains. -/
def markedRawEdgeChoiceCode {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) :
    Z × ((J → Bool) × (Σ prom : MarkedRawEdgePromotions s.2.2, MarkedRawEdgeFreshLabels prom)) :=
  (choice.target,(choice.store,⟨choice.promotions,choice.fresh⟩))

theorem markedRawEdgeChoiceCode_injective {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) :
    Function.Injective (markedRawEdgeChoiceCode hZ s) := by
  rintro ⟨ta,sa,pa,fa,hpa,hba⟩ ⟨tb,sb,pb,fb,hpb,hbb⟩ he
  change (ta,(sa,Sigma.mk pa fa))=(tb,(sb,Sigma.mk pb fb)) at he
  have ht := congrArg Prod.fst he
  cases ht
  have hp := congrArg Prod.snd he
  have hs := congrArg Prod.fst hp
  cases hs
  have hsig := congrArg Prod.snd hp
  cases hsig
  rfl

noncomputable instance markedRawEdgeFreshLabels_fintype {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B}
    (prom : MarkedRawEdgePromotions m) : Fintype (MarkedRawEdgeFreshLabels prom) := by
  classical
  letI : ∀ j, Fintype (match prom j with | none => ↥(P j) | some _ => PUnit) := fun j => by
    cases prom j <;> infer_instance
  unfold MarkedRawEdgeFreshLabels
  infer_instance

noncomputable instance markedRawEdgeChoice_fintype {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) :
    Fintype (MarkedRawEdgeChoice hZ s) := by
  classical
  exact Fintype.ofInjective _ (markedRawEdgeChoiceCode_injective hZ s)

/-- No old promotion leaves exactly the actual fresh tuple. -/
theorem markedRawEdgeTargetLast_none {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (m : MarkedRawMemory P B) (fresh : (j : J) → ↥(P j)) :
    markedRawEdgeTargetLast m (fun _ => none) fresh=fresh := rfl

/-- Literal clean choice: draw every target last label freshly, store none,
promote none and retain the actual old pending memory. -/
def markedRawCleanEdgeChoice {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (target : Z) (fresh : (j : J) → ↥(P j)) : MarkedRawEdgeChoice hZ s where
  target := target
  store := fun _ => false
  promotions := fun _ => none
  fresh := fresh
  promotion_hits := by intro j k hk; cases hk
  memory_bound := by
    simpa only [markedRawGhostSurvivors,markedRawEdgePromotionDeletion,Option.toFinset_none,
      Finset.sdiff_empty,Finset.card_univ,Fintype.card_fin,Bool.false_eq_true,ite_false,Nat.add_zero]
      using s.2.2.1.2

/-- The literal clean transition retains the same indexed memory, proved
from the actual update rather than assumed when matching operators. -/
theorem markedRawCleanEdgeChoice_memory {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (target : Z) (fresh : (j : J) → ↥(P j)) :
    markedRawEdgeTargetMemory hZ s (markedRawCleanEdgeChoice hZ s target fresh)=s.2.2 := by
  apply markedRawGhostTargetMemory_empty_eq
  · intro j
    rfl
  · intro j
    rfl

/-- The literal clean target is exactly the target summed by the previously
proved full raw clean action, including its old memory coordinates. -/
theorem markedRawCleanEdgeChoice_target {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (target : Z) (fresh : (j : J) → ↥(P j)) :
    markedRawEdgeTargetState hZ s (markedRawCleanEdgeChoice hZ s target fresh)=
      (target,((markedRawActiveSplit pads).symm (((markedRawActiveSplit pads) s.2.1).1,fresh),s.2.2)) := by
  unfold markedRawEdgeTargetState
  rw [markedRawCleanEdgeChoice_memory]
  rfl

end ArtinMatthews
