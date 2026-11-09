module

public import ArtinMatthews.MarkedMemoryHistoryBirthQuotient


set_option backward.privateInPublic true
@[expose] public section

/-! For disjoint actual prime bands, the exact ghost birth quotient is
also the quotient by global numeric-prime distinctness. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B}
  {del : MarkedRawGhostDeletion m}

def MarkedMemoryGhostBirthsGloballyAvoid (l : MarkedRawGhostBirthSizes m del)
    (forbidden : Finset Nat.Primes) (births : MarkedRawGhostBirthLabels l) : Prop :=
  Function.Injective (fun b : (Σ j : J, Fin (l.1 j : ℕ)) => (births b.1 b.2).1) ∧
    ∀ j k, (births j k).1 ∉ forbidden

theorem markedMemoryGhostBirthsAvoid_iff_global
    (hP : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (l : MarkedRawGhostBirthSizes m del) (forbidden : Finset Nat.Primes)
    (births : MarkedRawGhostBirthLabels l) :
    MarkedMemoryGhostBirthsAvoid l forbidden births ↔
      MarkedMemoryGhostBirthsGloballyAvoid l forbidden births := by
  constructor
  · rintro ⟨hinj,havoid⟩
    refine ⟨?_,havoid⟩
    rintro ⟨i,k⟩ ⟨j,r⟩ heq
    change (births i k).1 = (births j r).1 at heq
    have hij : i = j := by
      by_contra hne
      exact (Finset.disjoint_left.mp (hP i j hne)) (births i k).2
        (heq.symm ▸ (births j r).2)
    subst j
    have hkr : k = r := hinj i (Subtype.ext heq)
    subst r
    rfl
  · rintro ⟨hinj,havoid⟩
    refine ⟨?_,havoid⟩
    intro j a b hab
    have heq : (⟨j,a⟩ : Σ j : J, Fin (l.1 j : ℕ)) = ⟨j,b⟩ :=
      hinj (show (births j a).1 = (births j b).1 from congrArg Subtype.val hab)
    exact eq_of_heq (Sigma.mk.inj heq).2

/-- The actual signed quotient with the global birth-distinct predicate,
under the separately checked disjointness of the original prime bands. -/
theorem markedMemoryGhostBirths_unordered_global_sum
    (hP : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (l : MarkedRawGhostBirthSizes m del) (forbidden : Finset Nat.Primes)
    (f : MarkedRawMemory P B → ℂ) (hf : MarkedRawMemorySymmetric f) :
    (∑ births : MarkedRawGhostBirthLabels l,
      if MarkedMemoryGhostBirthsGloballyAvoid l forbidden births then
        ((markedRawGhostSignedCoefficient V qStage ρ m z hz del l *
          markedRawGhostBirthMass ν l births : ℝ) : ℂ) *
            f (markedRawGhostTargetMemory m z hz del l births)
      else 0) =
    ∑ S : (j : J) → MarkedMemoryBirthSets
        (MarkedMemoryAllowedBirthPrime (P := P) forbidden j) (l.1 j : ℕ),
      ((markedRawGhostSignedCoefficient V qStage ρ m z hz del l *
        (∏ j, ∏ p ∈ (S j).1, ν j p.1) : ℝ) : ℂ) *
          f (markedRawGhostTargetMemory m z hz del l
            (markedMemoryGhostBirthsOfEmbedding l forbidden (markedMemoryBirthFamilyCanonical S))) := by
  simp_rw [← markedMemoryGhostBirthsAvoid_iff_global hP]
  exact markedMemoryGhostBirths_unordered_sum ν V qStage ρ m z hz del l forbidden f hf

end
end ArtinMatthews
