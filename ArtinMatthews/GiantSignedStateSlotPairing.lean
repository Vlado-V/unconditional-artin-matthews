module

public import ArtinMatthews.GiantSignedRawSlotAverage
public import ArtinMatthews.IdealSlotSymmetry


set_option backward.privateInPublic true
@[expose] public section

/-! The full endpoint average can be moved across the actual weighted
pairing at each fixed pending memory. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}

theorem giantSignedStateSlotAverage_split
    (f : GiantSignedState PS PB M → ℂ)
    (s : GiantTwoSidedResidueState PS M) (a : MarkedPhysicalMarking PB M)
    (m : GiantSignedMemory PB) :
    giantSignedStateSlotAverage PS f (s,a,m) =
      (Fintype.card (S → Equiv.Perm (Fin M)) : ℂ)⁻¹ *
        ∑ π : S → Equiv.Perm (Fin M),
          idealSlotAverage (fun b => f (giantTwoSidedResiduePermute π s,b,m)) a := by
  simp only [giantSignedStateSlotAverage, GiantSignedStateSlotPermutations,
    Fintype.card_prod, Nat.cast_mul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_natCast, mul_inv, Fintype.sum_prod_type, idealSlotAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_congr rfl
  intro τ _
  change ((Fintype.card (S → Equiv.Perm (Fin M)) : ℂ)⁻¹ *
      (Fintype.card (B → Equiv.Perm (Fin M)) : ℂ)⁻¹) *
        f (giantTwoSidedResiduePermute π s,giantTwoSidedPermuteLabels τ a,m) = _
  ring

theorem giantSignedStateSlotAverage_bigSymmetric
    (f : GiantSignedState PS PB M → ℂ)
    (s : GiantTwoSidedResidueState PS M) (m : GiantSignedMemory PB) :
    IdealSymmetric (fun a => giantSignedStateSlotAverage PS f (s,a,m)) := by
  intro τ a
  simp only [giantSignedStateSlotAverage_split]
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  exact idealSlotAverage_symmetric (fun b => f (giantTwoSidedResiduePermute π s,b,m)) τ a

variable [Fintype (GiantTwoSidedResidueState PS M)]

def giantSignedStateFiberPairing (ν : ∀ g, PB g → ℝ)
    (w₁ w₂ : GiantSignedState PS PB M → ℂ) (m : GiantSignedMemory PB) : ℂ :=
  ∑ p : GiantTwoSidedResidueState PS M × MarkedPhysicalMarking PB M,
    (giantSignedStateMass PS ν (p.1,p.2,m) : ℂ) * star (w₁ (p.1,p.2,m)) * w₂ (p.1,p.2,m)

theorem giantSignedStateFiberPairing_slotAverage (ν : ∀ g, PB g → ℝ)
    (w₁ w₂ : GiantSignedState PS PB M → ℂ) (m : GiantSignedMemory PB) :
    giantSignedStateFiberPairing PS ν w₁ (giantSignedStateSlotAverage PS w₂) m =
      giantSignedStateFiberPairing PS ν (giantSignedStateSlotAverage PS w₁) w₂ m := by
  let X := GiantTwoSidedResidueState PS M × MarkedPhysicalMarking PB M
  let A := GiantSignedStateSlotPermutations S B M
  let F (p : X) : GiantSignedState PS PB M := (p.1,p.2,m)
  let W : ℂ := (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ)
  have hW : star W = W := by simp only [W, Complex.star_def, Complex.conj_ofReal]
  let R (π : A) (p : X) : ℂ :=
    (giantSignedStateMass PS ν (F p) : ℂ) *
      (star (w₁ ((giantSignedStatePermute PS π.1 π.2).symm (F p))) * W) * w₂ (F p)
  have hleft : giantSignedStateFiberPairing PS ν w₁ (giantSignedStateSlotAverage PS w₂) m =
      ∑ π : A, ∑ p : X, (giantSignedStateMass PS ν (F p) : ℂ) * star (w₁ (F p)) *
        (W * w₂ (giantSignedStatePermute PS π.1 π.2 (F p))) := by
    unfold giantSignedStateFiberPairing giantSignedStateSlotAverage
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  have hright : giantSignedStateFiberPairing PS ν (giantSignedStateSlotAverage PS w₁) w₂ m =
      ∑ π : A, ∑ p : X, R π p := by
    unfold giantSignedStateFiberPairing
    simp_rw [← giantSignedStateSlotAverage_inverse PS w₁]
    simp only [star_sum, star_mul, Finset.mul_sum, Finset.sum_mul]
    change (∑ p : X, ∑ π : A, (giantSignedStateMass PS ν (F p) : ℂ) *
      (star (w₁ ((giantSignedStatePermute PS π.1 π.2).symm (F p))) * star W) * w₂ (F p)) = _
    simp only [hW, R]
    exact Finset.sum_comm
  rw [hleft, hright]
  apply Finset.sum_congr rfl
  intro π _
  let e : X ≃ X := Equiv.prodCongr (giantTwoSidedResiduePermute π.1)
    (giantSignedGroupedTuplePermutation π.2)
  calc
    _ = ∑ p : X, R π (e p) := by
      apply Finset.sum_congr rfl
      intro p _
      have hp : F (e p) = giantSignedStatePermute PS π.1 π.2 (F p) := rfl
      simp only [R, hp, Equiv.symm_apply_apply, giantSignedStateMass_slot_permute]
      ring
    _ = _ := e.sum_comp (R π)

end
end ArtinMatthews
