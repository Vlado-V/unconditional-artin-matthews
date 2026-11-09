module

public import ArtinMatthews.MarkedMinorArcRawGhostAction
public import ArtinMatthews.MarkedMinorArcRawMemoryExtension
public import Mathlib.Logic.Equiv.Fin.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Pending-index transport for the literal ghost operation. Masks and
survivors are transported by indices, with no distinctness of values. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews

/-- A genuine index equivalence suffices for symmetric-memory equality,
even when the equal group-size vectors were constructed differently. -/
theorem markedRawMemorySymmetric_equiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} {f : MarkedRawMemory P B → ℂ}
    (hf : MarkedRawMemorySymmetric f) (m m' : MarkedRawMemory P B)
    (e : (j : J) → Fin (m'.1.1 j : ℕ) ≃ Fin (m.1.1 j : ℕ))
    (he : ∀ j i, m'.2 j i = m.2 j (e j i)) : f m'=f m := by
  have hs : m'.1=m.1 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    simpa only [Fintype.card_fin] using Fintype.card_congr (e j)
  rcases m with ⟨k,a⟩
  rcases m' with ⟨k',a'⟩
  dsimp only at hs
  subst k'
  have hh : (⟨k,a'⟩ : MarkedRawMemory P B)=markedRawMemoryPermute ⟨k,a⟩ e := by
    congr 1
    funext j i
    exact he j i
  rw [hh]
  exact hf ⟨k,a⟩ e

/-- Permuting an old tuple pulls each chosen deletion index back. -/
def markedRawGhostDeletionPermute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ)))
    (del : MarkedRawGhostDeletion m) : MarkedRawGhostDeletion (markedRawMemoryPermute m σ) :=
  fun j => (del j).map (σ j).symm.toEmbedding

def markedRawGhostDeletionPermuteEquiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) :
    MarkedRawGhostDeletion m ≃ MarkedRawGhostDeletion (markedRawMemoryPermute m σ) :=
  Equiv.piCongrRight (fun j => (σ j).symm.finsetCongr)

theorem markedRawGhostDeletionPermute_card {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ)))
    (del : MarkedRawGhostDeletion m) (j : J) :
    (markedRawGhostDeletionPermute m σ del j).card=(del j).card := Finset.card_map _

/-- The actual old hit set transforms by the same old-index bijection. -/
theorem markedRawGhostHitIndices_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ)))
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (j : J) :
    markedRawGroupHitIndices (markedRawMemoryPermute m σ) j z hz =
      (markedRawGroupHitIndices m j z hz).map (σ j).symm.toEmbedding := by
  classical
  change (Finset.univ.filter (fun k => MarkedRawParticleHits (P j) z hz (m.2 j (σ j k)))) =
    (markedRawGroupHitIndices m j z hz).map (σ j).symm.toEmbedding
  ext i
  simp only [markedRawGroupHitIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map_equiv, Equiv.symm_symm]

theorem markedRawGhostDeletionAllowed_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ)))
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m) :
    MarkedRawGhostDeletionAllowed (markedRawMemoryPermute m σ) z hz
      (markedRawGhostDeletionPermute m σ del) ↔ MarkedRawGhostDeletionAllowed m z hz del := by
  simp only [MarkedRawGhostDeletionAllowed, markedRawGhostHitIndices_permute,
    markedRawGhostDeletionPermute]
  apply forall_congr'
  intro j
  exact Finset.map_subset_map

theorem markedRawGhostSurvivors_permute_card {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ)))
    (del : MarkedRawGhostDeletion m) (j : J) :
    (markedRawGhostSurvivors (markedRawMemoryPermute m σ) (markedRawGhostDeletionPermute m σ del) j).card=
      (markedRawGhostSurvivors m del j).card := by
  simp only [markedRawGhostSurvivors, Finset.card_sdiff, Finset.inter_univ,
    markedRawGhostDeletionPermute_card]
  rfl

/-- The concrete survivor-index bijection, before translating either
side to its canonical increasing enumeration. -/
def markedRawGhostSurvivorSubsetEquiv {k : ℕ} (σ : Equiv.Perm (Fin k))
    (S : Finset (Fin k)) : ↥(Finset.univ \ S.map σ.symm.toEmbedding) ≃ ↥(Finset.univ \ S) where
  toFun i := ⟨σ i.1,by
    have hi := (Finset.mem_sdiff.mp i.2).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,by simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using hi⟩⟩
  invFun i := ⟨σ.symm i.1,by
    have hi := (Finset.mem_sdiff.mp i.2).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,by simpa only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply] using hi⟩⟩
  left_inv i := by ext; simp
  right_inv i := by ext; simp

def markedRawGhostSurvivorIndexEquiv {k : ℕ} (σ : Equiv.Perm (Fin k))
    (S : Finset (Fin k)) :
    Fin (Finset.univ \ S.map σ.symm.toEmbedding).card ≃ Fin (Finset.univ \ S).card :=
  ((Finset.univ \ S.map σ.symm.toEmbedding).orderIsoOfFin rfl).toEquiv.trans
    ((markedRawGhostSurvivorSubsetEquiv σ S).trans
      ((Finset.univ \ S).orderIsoOfFin rfl).toEquiv.symm)

theorem markedRawGhostSurvivorIndexEquiv_apply {k : ℕ} (σ : Equiv.Perm (Fin k))
    (S : Finset (Fin k)) (i : Fin (Finset.univ \ S.map σ.symm.toEmbedding).card) :
    (Finset.univ \ S).orderEmbOfFin rfl (markedRawGhostSurvivorIndexEquiv σ S i)=
      σ ((Finset.univ \ S.map σ.symm.toEmbedding).orderEmbOfFin rfl i) := by
  have hh := ((Finset.univ \ S).orderIsoOfFin rfl).toEquiv.apply_symm_apply
    (markedRawGhostSurvivorSubsetEquiv σ S (((Finset.univ \ S.map σ.symm.toEmbedding).orderIsoOfFin rfl) i))
  exact congrArg Subtype.val hh

end ArtinMatthews
