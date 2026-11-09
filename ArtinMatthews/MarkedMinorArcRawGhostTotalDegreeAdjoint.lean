module

public import ArtinMatthews.MarkedMinorArcRawGhostDegreeChoices
public import ArtinMatthews.MarkedMinorArcRawGhostGroupedDegreeAdjoint


set_option backward.privateInPublic true
@[expose] public section

/-! Transposing the genuine grouped ghost components with both original
total-memory restrictions retained.  Exchanging deleted and born degrees
is an exact involution of the finite allowed degree family. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Exchange the actual deleted and born degrees, including the two
literal total-memory bounds. -/
def markedRawGhostDegreesSwap {J : Type*} [Fintype J] {B : ℕ} :
    MarkedRawGhostDegrees J B ≃ MarkedRawGhostDegrees J B where
  toFun t := ⟨t.survivors,t.born,t.deleted,t.target_le,t.source_le⟩
  invFun t := ⟨t.survivors,t.born,t.deleted,t.target_le,t.source_le⟩
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl

/-- Exact full finite-degree transpose.  Both source and target satisfy
the original sum-of-degrees cutoff, rather than independent per-group
cutoffs.  The functions can couple every prime group. -/
theorem markedRawGhost_total_degree_transpose
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℂ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (B : ℕ) (δ γ s : J → ℂ)
    (g f : (k : J → ℕ) → (∑ j,k j) ≤ B →
      ((j : J) → Fin (k j) → MarkedRawParticle (P j)) → ℂ)
    (hg : ∀ k hk,MarkedRawGroupedTupleSymmetric k (g k hk))
    (hf : ∀ k hk,MarkedRawGroupedTupleSymmetric k (f k hk)) :
    (∑ t : MarkedRawGhostDegrees J B,
      ∑ a : (j : J) → Fin (t.survivors j+t.deleted j) → MarkedRawParticle (P j),
        ((∏ j,∏ i,ν j (a j i).1)/(∏ j,(Nat.factorial (t.survivors j+t.deleted j) : ℂ)))*
          g (fun j => t.survivors j+t.deleted j) t.source_le a*
          markedRawGhostGroupedDegreeComponent P ν z hz t.survivors t.deleted t.born δ γ s
            (f (fun j => t.survivors j+t.born j) t.target_le) a)=
      ∑ t : MarkedRawGhostDegrees J B,
        ∑ a : (j : J) → Fin (t.survivors j+t.deleted j) → MarkedRawParticle (P j),
          ((∏ j,∏ i,ν j (a j i).1)/(∏ j,(Nat.factorial (t.survivors j+t.deleted j) : ℂ)))*
            f (fun j => t.survivors j+t.deleted j) t.source_le a*
            markedRawGhostGroupedDegreeComponent P ν z hz t.survivors t.deleted t.born γ δ s
              (g (fun j => t.survivors j+t.born j) t.target_le) a := by
  classical
  rw [← Equiv.sum_comp (markedRawGhostDegreesSwap (J := J) (B := B))]
  apply Finset.sum_congr rfl
  intro t _
  exact markedRawGhost_grouped_degree_transpose P ν z hz
    t.survivors t.born t.deleted δ γ s
      (g _ t.target_le) (hg _ t.target_le) (f _ t.source_le) (hf _ t.source_le)

end ArtinMatthews
