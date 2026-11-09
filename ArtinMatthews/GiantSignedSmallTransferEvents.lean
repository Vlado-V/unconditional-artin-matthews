module

public import ArtinMatthews.GiantSignedSmallOmissionCongruence


set_option backward.privateInPublic true
@[expose] public section

/-! Literal signed transfer congruences retain the source exclusion.
Disjoint small and pending-prime bands supply the full-product unit. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def GiantSignedSmallTransferEvent {S : Type*} [Fintype S]
    {P : S → Finset ℕ} {M ell p : ℕ}
    (a : MarkedPhysicalMarking P M) (r u : ZMod p) (DBig : ℕ)
    (U : GiantSignedSmallOmission S M ell) : Prop :=
  r + (u * (DBig : ZMod p)) * (giantSignedSmallCopiedProduct a U : ZMod p) = 0 ∧
    ¬ p ∣ DBig * giantSignedSmallCopiedProduct a U


section Events
variable {S : Type*} [Fintype S] {P : S → Finset ℕ} {M ell p : ℕ}
variable [Fact p.Prime]

theorem giantSignedSmallFull_ne_zero_mod
    (hP : ∀ g q, q ∈ P g → q.Prime) (a : MarkedPhysicalMarking P M)
    (Q : Finset ℕ) (hp : p ∈ Q) (hdis : ∀ g, Disjoint (P g) Q) :
    (markedPhysicalMarkingProduct a : ZMod p) ≠ 0 := by
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
  unfold markedPhysicalMarkingProduct at hd
  obtain ⟨g, _, hg⟩ := ((Fact.out : p.Prime).prime.dvd_finsetProd_iff _).mp hd
  obtain ⟨i, _, hi⟩ := ((Fact.out : p.Prime).prime.dvd_finsetProd_iff _).mp hg
  have he : p = (a g i : ℕ) :=
    (Nat.prime_dvd_prime_iff_eq Fact.out (hP g _ (a g i).property)).mp hi
  exact Finset.disjoint_left.mp (hdis g) (a g i).property (he ▸ hp)


theorem giantSignedSmallTransfer_coefficient_ne_zero
    (a : MarkedPhysicalMarking P M) (r u : ZMod p) (hu : u ≠ 0) (DBig : ℕ)
    (U : GiantSignedSmallOmission S M ell)
    (h : GiantSignedSmallTransferEvent a r u DBig U) : u * (DBig : ZMod p) ≠ 0 := by
  have hD : (DBig : ZMod p) ≠ 0 := by
    intro hz
    apply h.2
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_mul, hz, zero_mul]
  exact mul_ne_zero hu hD

theorem giantSignedSmallTransfer_residue_ne_zero
    (a : MarkedPhysicalMarking P M) (r u : ZMod p) (hu : u ≠ 0) (DBig : ℕ)
    (hF : (markedPhysicalMarkingProduct a : ZMod p) ≠ 0)
    (U : GiantSignedSmallOmission S M ell)
    (h : GiantSignedSmallTransferEvent a r u DBig U) : r ≠ 0 :=
  giantSignedSmallPromotion_residue_ne_zero a r (u * (DBig : ZMod p))
    (giantSignedSmallTransfer_coefficient_ne_zero a r u hu DBig U h) hF U h.1

theorem giantSignedSmallTransfer_unique
    (hP : ∀ g q, q ∈ P g → q.Prime)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a)
    (r u : ZMod p) (hu : u ≠ 0) (DBig : ℕ)
    (hF : (markedPhysicalMarkingProduct a : ZMod p) ≠ 0)
    (hbound : ∀ U : GiantSignedSmallOmission S M ell, giantSignedSmallOmittedProduct a U < p)
    (U V : GiantSignedSmallOmission S M ell)
    (hU : GiantSignedSmallTransferEvent a r u DBig U)
    (hV : GiantSignedSmallTransferEvent a r u DBig V) : U = V :=
  giantSignedSmallPromotion_unique hP hdis a ha r (u * (DBig : ZMod p))
    (giantSignedSmallTransfer_coefficient_ne_zero a r u hu DBig U hU) hF hbound U V hU.1 hV.1

end Events

section Steps
variable {p : ℕ}

theorem giantSignedPositiveStep_ne_zero_mod (kStep : ℕ) (hk : 0 < kStep) (hkp : kStep < p) :
    (kStep : ZMod p) ≠ 0 := by
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
  exact (not_le_of_gt hkp) (Nat.le_of_dvd hk hd)

theorem giantSignedSignedStep_ne_zero_mod (kStep : ℕ) (hk : 0 < kStep) (hkp : kStep < p)
    (sign : ℤ) (hsign : sign = 1 ∨ sign = -1) : ((sign * kStep : ℤ) : ZMod p) ≠ 0 := by
  have hstep := giantSignedPositiveStep_ne_zero_mod kStep hk hkp
  rcases hsign with rfl | rfl
  · simpa only [one_mul, Int.cast_natCast] using hstep
  · simpa only [neg_one_mul, Int.cast_neg, Int.cast_natCast] using neg_ne_zero.mpr hstep

end Steps
end
end ArtinMatthews
