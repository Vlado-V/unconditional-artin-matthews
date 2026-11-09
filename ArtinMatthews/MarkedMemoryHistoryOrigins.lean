module

public import ArtinMatthews.MarkedMinorArcRawGhostState
public import Mathlib.Logic.Equiv.Fin.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Literal indexed provenance through a ghost update. An origin identifies
an old index or a newly performed birth index, never its numeric prime value.
Consequently repeated particle values remain separate throughout. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Every actual target memory index comes from exactly one surviving old
index or one ordered birth index, in the original survivor-then-birth order. -/
noncomputable def markedMemoryGhostOrigin {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del) (j : J) :
    Fin ((markedRawGhostTargetSizes m del l).1 j : ℕ) ≃
      (↥(markedRawGhostSurvivors m del j) ⊕ Fin (l.1 j : ℕ)) :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr
    ((markedRawGhostSurvivors m del j).orderIsoOfFin rfl).toEquiv (Equiv.refl _))

theorem markedMemoryGhostOrigin_old {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) (j : J)
    (i : ↥(markedRawGhostSurvivors m del j)) :
    (markedRawGhostTargetMemory m z hz del l births).2 j
      ((markedMemoryGhostOrigin m del l j).symm (Sum.inl i)) = m.2 j i.1 := by
  change @Fin.addCases (markedRawGhostSurvivors m del j).card (l.1 j : ℕ)
    (fun _ => MarkedRawParticle (P j))
    (fun k => m.2 j ((markedRawGhostSurvivors m del j).orderEmbOfFin rfl k))
    (fun k => markedRawAnchoredParticle (P j) (births j k) z hz)
    (Fin.castAdd (l.1 j : ℕ)
    (((markedRawGhostSurvivors m del j).orderIsoOfFin rfl).symm i)) = _
  rw [Fin.addCases_left]
  apply congrArg (m.2 j)
  exact congrArg Subtype.val (((markedRawGhostSurvivors m del j).orderIsoOfFin rfl).apply_symm_apply i)

theorem markedMemoryGhostOrigin_birth {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) (j : J)
    (i : Fin (l.1 j : ℕ)) :
    (markedRawGhostTargetMemory m z hz del l births).2 j
      ((markedMemoryGhostOrigin m del l j).symm (Sum.inr i)) =
        markedRawAnchoredParticle (P j) (births j i) z hz := by
  change @Fin.addCases (markedRawGhostSurvivors m del j).card (l.1 j : ℕ)
    (fun _ => MarkedRawParticle (P j))
    (fun k => m.2 j ((markedRawGhostSurvivors m del j).orderEmbOfFin rfl k))
    (fun k => markedRawAnchoredParticle (P j) (births j k) z hz)
    (Fin.natAdd (markedRawGhostSurvivors m del j).card i) = _
  exact Fin.addCases_right i

/-- The exact product over actual target particles factors through their
indexed origins. This holds with repeated old or new prime values. -/
theorem markedMemoryGhostOrigin_product {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) (j : J)
    (f : MarkedRawParticle (P j) → ℂ) :
    (∏ i, f ((markedRawGhostTargetMemory m z hz del l births).2 j i)) =
      (∏ i : ↥(markedRawGhostSurvivors m del j), f (m.2 j i.1))*
        ∏ i, f (markedRawAnchoredParticle (P j) (births j i) z hz) := by
  classical
  have he := Equiv.prod_comp (markedMemoryGhostOrigin m del l j).symm
    (fun i => f ((markedRawGhostTargetMemory m z hz del l births).2 j i))
  calc
    _ = _ := he.symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      simp only [markedMemoryGhostOrigin_old,markedMemoryGhostOrigin_birth]

end ArtinMatthews
