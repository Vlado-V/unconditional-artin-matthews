module

public import ArtinMatthews.GiantSignedEdgeReversal


set_option backward.privateInPublic true
@[expose] public section

/-! The one-sided promotion ban is retained in the literal row and is
transported as part of the complete test under reversal. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

section BanJoint
variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
variable [∀ j, ∀ p : P j, NeZero p.val] {t : J → ℕ}

def giantSignedEdgeBanTest (D : ℕ) (T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℂ)
    (source target : GiantSignedPrimeTuple P t) (old out : GiantSignedMemory P) : ℂ :=
  if GiantSignedEdgePromotionBan D T target then F source target old out else 0

def giantSignedEdgeBannedPairing (ν : (j : J) → P j → ℂ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (D : ℕ) (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℂ) : ℂ :=
  ∑ source : GiantSignedPrimeTuple P t, ∑ target : GiantSignedPrimeTuple P t,
    giantSignedFreePrimeMass ν source * giantSignedPromotionCharge V (fun j => (T j).card) *
      giantSignedFreshPrimeMass ν T target *
      ∑ old : GiantSignedParticleTuple P (fun j => n j + (T j).card),
        giantSignedDegreeMass ν old *
          ∑ e : (j : J) → Fin (T j).card ↪ Fin (n j + (T j).card),
            if GiantSignedEdgeHits d ⟨fun j => n j + (T j).card, old⟩ target ⟨S, T, e⟩ ∧
                GiantSignedEdgePromotionBan D T target then
              giantSignedEdgeDampedTest ρ (F source target)
                ⟨fun j => n j + (T j).card, old⟩
                (giantSignedEdgeTarget d ⟨fun j => n j + (T j).card, old⟩ source ⟨S, T, e⟩)
            else 0

theorem giantSignedEdgeBannedPairing_eq_test (ν : (j : J) → P j → ℂ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (D : ℕ) (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℂ) :
    giantSignedEdgeBannedPairing ν V ρ d D n S T F =
      giantSignedEdgeStorePromotePairing ν V ρ d n S T (giantSignedEdgeBanTest D T F) := by
  unfold giantSignedEdgeBannedPairing giantSignedEdgeStorePromotePairing
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro target _
  congr 1
  apply Finset.sum_congr rfl
  intro old _
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases hh : GiantSignedEdgeHits d ⟨fun j => n j + (T j).card, old⟩ target ⟨S, T, e⟩ <;>
    by_cases hb : GiantSignedEdgePromotionBan D T target <;>
      simp [hh, hb, giantSignedEdgeDampedTest, giantSignedEdgeBanTest]

theorem giantSignedEdgeBannedPairing_reverse
    (ν : (j : J) → P j → ℂ) (V : J → ℝ) (hV : ∀ j, V j ≠ 0)
    (ρ : ℝ) (d : ℤ) (D : ℕ) (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℂ)
    (hSource : ∀ source target out,
      GiantSignedMemorySymmetric (fun old => F source target old out))
    (hTarget : ∀ source target old,
      GiantSignedMemorySymmetric (fun out => F source target old out)) :
    giantSignedEdgeBannedPairing ν V ρ d D n S T F =
      (∏ j, (V j : ℂ) ^ (S j).card / (V j : ℂ) ^ (T j).card) *
        giantSignedEdgeStorePromotePairing ν V ρ (-d) n T S
          (fun target source out old =>
            if GiantSignedEdgePromotionBan D T target then F source target old out else 0) := by
  have hs : ∀ source target out, GiantSignedMemorySymmetric
      (fun old => giantSignedEdgeBanTest D T F source target old out) := by
    intro source target out old σ
    by_cases hb : GiantSignedEdgePromotionBan D T target
    · simp only [giantSignedEdgeBanTest, hb, ite_true]
      exact hSource source target out old σ
    · simp only [giantSignedEdgeBanTest, hb, ite_false]
  have ht : ∀ source target old, GiantSignedMemorySymmetric
      (fun out => giantSignedEdgeBanTest D T F source target old out) := by
    intro source target old out σ
    by_cases hb : GiantSignedEdgePromotionBan D T target
    · simp only [giantSignedEdgeBanTest, hb, ite_true]
      exact hTarget source target old out σ
    · simp only [giantSignedEdgeBanTest, hb, ite_false]
  rw [giantSignedEdgeBannedPairing_eq_test]
  exact giantSignedEdgeStorePromotePairing_reverse ν V hV ρ d n S T
    (giantSignedEdgeBanTest D T F) hs ht

end BanJoint
end
end ArtinMatthews
