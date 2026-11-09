module

public import ArtinMatthews.GiantSignedEdgeStorePromote


set_option backward.privateInPublic true
@[expose] public section

/-! Reversal interchanges the two endpoint memories and the two selected
slot sets. Its exact scalar is the difference of promotion charges. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedPromotionCharge_reverse {J : Type*} [Fintype J] (V : J → ℝ) (hV : ∀ j, V j ≠ 0)
    (a b : J → ℕ) :
    giantSignedPromotionCharge V a =
      (∏ j, (V j : ℂ) ^ b j / (V j : ℂ) ^ a j) * giantSignedPromotionCharge V b := by
  unfold giantSignedPromotionCharge
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hv : (V j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hV j)
  rw [inv_pow, inv_pow]
  field_simp [hv]

section Reversal
variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
variable [∀ j, ∀ p : P j, NeZero p.val]
variable {t : J → ℕ}

theorem giantSignedEdgeJointKernel_reverse
    (ν : (j : J) → P j → ℂ) (ρ : ℝ) (d : ℤ)
    (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℂ) :
    giantSignedEdgeJointKernel ν ρ d n S T F =
      giantSignedEdgeJointKernel ν ρ (-d) n T S
        (fun target source out old => F source target old out) := by
  classical
  unfold giantSignedEdgeJointKernel
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro target _
  rw [mul_comm (giantSignedFreePrimeMass ν target)]
  congr 1
  let E := giantSignedTupleTranslate (P := P) d n
  conv_rhs => rw [← Equiv.sum_comp E]
  apply Finset.sum_congr rfl
  intro u _
  have hm : giantSignedDegreeMass ν (E u) = giantSignedDegreeMass ν u := rfl
  rw [hm]
  congr 1
  unfold giantSignedEdgeDampedTest
  rw [giantSignedEdgeInput_reverse, giantSignedEdgeOutput_reverse]
  ring

/-- Exact coupled-test reversal. The factor is retained when the source
and target promotion counts differ. -/
theorem giantSignedEdgeStorePromotePairing_reverse
    (ν : (j : J) → P j → ℂ) (V : J → ℝ) (hV : ∀ j, V j ≠ 0)
    (ρ : ℝ) (d : ℤ) (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℂ)
    (hSource : ∀ source target out,
      GiantSignedMemorySymmetric (fun old => F source target old out))
    (hTarget : ∀ source target old,
      GiantSignedMemorySymmetric (fun out => F source target old out)) :
    giantSignedEdgeStorePromotePairing ν V ρ d n S T F =
      (∏ j, (V j : ℂ) ^ (S j).card / (V j : ℂ) ^ (T j).card) *
        giantSignedEdgeStorePromotePairing ν V ρ (-d) n T S
          (fun target source out old => F source target old out) := by
  rw [giantSignedEdgeStorePromotePairing_eq_joint ν V ρ d n S T F hSource,
    giantSignedEdgeStorePromotePairing_eq_joint ν V ρ (-d) n T S
      (fun target source out old => F source target old out)
      (fun target source old => hTarget source target old),
    giantSignedEdgeJointKernel_reverse ν ρ d n S T F,
    giantSignedPromotionCharge_reverse V hV (fun j => (T j).card) (fun j => (S j).card)]
  ring

/-- All survivor degrees are retained in this actual store/promote sector. -/
def giantSignedEdgeAllDegreePairing
    (ν : (j : J) → P j → ℂ) (V : J → ℝ) (ρ : ℝ) (d : ℤ)
    (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℂ) : ℂ :=
  ∑' n : J → ℕ, giantSignedEdgeStorePromotePairing ν V ρ d n S T F

theorem giantSignedEdgeAllDegreePairing_eq_joint
    (ν : (j : J) → P j → ℂ) (V : J → ℝ) (ρ : ℝ) (d : ℤ)
    (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℂ)
    (hF : ∀ source target out, GiantSignedMemorySymmetric (fun old => F source target old out)) :
    giantSignedEdgeAllDegreePairing ν V ρ d S T F =
      giantSignedPromotionCharge V (fun j => (T j).card) *
        ∑' n : J → ℕ, giantSignedEdgeJointKernel ν ρ d n S T F := by
  unfold giantSignedEdgeAllDegreePairing
  rw [← tsum_mul_left]
  exact tsum_congr fun n => giantSignedEdgeStorePromotePairing_eq_joint ν V ρ d n S T F hF

theorem giantSignedEdgeAllDegreePairing_reverse
    (ν : (j : J) → P j → ℂ) (V : J → ℝ) (hV : ∀ j, V j ≠ 0)
    (ρ : ℝ) (d : ℤ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℂ)
    (hSource : ∀ source target out,
      GiantSignedMemorySymmetric (fun old => F source target old out))
    (hTarget : ∀ source target old,
      GiantSignedMemorySymmetric (fun out => F source target old out)) :
    giantSignedEdgeAllDegreePairing ν V ρ d S T F =
      (∏ j, (V j : ℂ) ^ (S j).card / (V j : ℂ) ^ (T j).card) *
        giantSignedEdgeAllDegreePairing ν V ρ (-d) T S
          (fun target source out old => F source target old out) := by
  unfold giantSignedEdgeAllDegreePairing
  rw [← tsum_mul_left]
  exact tsum_congr fun n =>
    giantSignedEdgeStorePromotePairing_reverse ν V hV ρ d n S T F hSource hTarget

end Reversal
end
end ArtinMatthews
