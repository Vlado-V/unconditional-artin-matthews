module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The predecessor and product hits on an ordered tuple have literal
residue tests at every selected prime. -/

namespace ArtinMatthews
open Finset
open scoped BigOperators

inductive GiantCandidateHitSide where
  | predecessor
  | product
  deriving DecidableEq

def giantCandidatePrimeHit (side : GiantCandidateHitSide) (p v : ℕ) : Prop :=
  match side with
  | .predecessor => p ∣ v-1
  | .product => p ∣ v

instance (side : GiantCandidateHitSide) (p v : ℕ) : Decidable (giantCandidatePrimeHit side p v) :=
  match side with
  | .predecessor => inferInstanceAs (Decidable (p ∣ v-1))
  | .product => inferInstanceAs (Decidable (p ∣ v))

def giantCandidatePrimeResidueHit {p j : ℕ} (side : GiantCandidateHitSide) (t : Fin j → ZMod p) : Prop :=
  match side with
  | .predecessor => (∏ i,t i)=1
  | .product => (∏ i,t i)=0

instance {p j : ℕ} (side : GiantCandidateHitSide) (t : Fin j → ZMod p) :
    Decidable (giantCandidatePrimeResidueHit side t) :=
  match side with
  | .predecessor => inferInstanceAs (Decidable ((∏ i,t i)=1))
  | .product => inferInstanceAs (Decidable ((∏ i,t i)=0))

theorem giantCandidatePrimeHit_iff_residue (side : GiantCandidateHitSide) (p : ℕ)
    {j : ℕ} (t : Fin j → ℕ) (ht : 0 < ∏ i,t i) :
    giantCandidatePrimeHit side p (∏ i,t i) ↔
      giantCandidatePrimeResidueHit side (fun i => (t i:ZMod p)) := by
  cases side
  · change p ∣ (∏ i,t i)-1 ↔ (∏ i,(t i:ZMod p))=1
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.succ_le_of_lt ht),
      Nat.cast_one,Nat.cast_prod,sub_eq_zero]
  · change p ∣ (∏ i,t i) ↔ (∏ i,(t i:ZMod p))=0
    rw [← ZMod.natCast_eq_zero_iff,Nat.cast_prod]

noncomputable def giantCandidatePrimeHitMask (p j : ℕ) [NeZero p] (side : GiantCandidateHitSide) :
    Finset (Fin j → ZMod p) :=
  univ.filter (giantCandidatePrimeResidueHit side)

theorem mem_giantCandidatePrimeHitMask {p j : ℕ} [NeZero p] (side : GiantCandidateHitSide)
    (t : Fin j → ZMod p) :
    t∈giantCandidatePrimeHitMask p j side ↔ giantCandidatePrimeResidueHit side t := by
  simp only [giantCandidatePrimeHitMask,mem_filter,mem_univ,true_and]

end ArtinMatthews
