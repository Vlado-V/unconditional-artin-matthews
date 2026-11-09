module

public import ArtinMatthews.MarkedMinorArcRawMemoryBulkFactorial
public import ArtinMatthews.MarkedMinorArcRawMemoryAnchors


set_option backward.privateInPublic true
@[expose] public section

/-! Actual unordered ghost deletion/anchored-creation adjoint integration.
Both factorials are derived from the actual indexed choices, and projective
anchors retain counting measure. Symmetric source functions are explicit. -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Genuine actual-particle batch adjoint. The left sums unordered eligible
old-index batches; the right integrates the corresponding ordered anchored
prime birth batch against ν^d/d!, with survivor measure λ^n/n!. -/
theorem markedRawGhost_batch_delete_pairing (P : Finset Nat.Primes) (ν : P → ℂ)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (n d : ℕ)
    (g : (Fin (n+d) → MarkedRawParticle P) → ℂ)
    (hg : MarkedRawTupleSymmetric (n+d) g) (f : (Fin n → MarkedRawParticle P) → ℂ) :
    (∑ a : Fin (n+d) → MarkedRawParticle P,
      ((∏ i, ν (a i).1)/(Nat.factorial (n+d) : ℂ))*g a*
        ∑ S : MarkedRawDeletionBatch (n+d) d,
          (∏ i, if MarkedRawParticleHits P z hz
            (markedRawDeletedTupleCast S.1 (markedRawDeletionBatch_deleted_card S) a i) then (1:ℂ) else 0)*
            f (markedRawSurvivorTupleCast S.1 (markedRawDeletionBatch_survivor_card rfl S) a))=
      ∑ survivors : Fin n → MarkedRawParticle P,
        ((∏ i, ν (survivors i).1)/(Nat.factorial n : ℂ))*f survivors*
          ∑ births : Fin d → P, ((∏ i, ν (births i))/(Nat.factorial d : ℂ))*
            g (Fin.addCases survivors (markedRawAnchoredBatch P z hz d births)) := by
  classical
  have hn : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hd : (Nat.factorial d : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hh := markedRawMemory_factorial_batch_delete (hk := rfl) (fun a : MarkedRawParticle P => ν a.1) g hg
    (fun deleted survivors => (∏ i, if MarkedRawParticleHits P z hz (deleted i) then (1:ℂ) else 0)*f survivors)
  simp only [Fin.cast_eq_self] at hh
  rw [hh,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro survivors _
  calc
    _ = ((∏ i, ν (survivors i).1)/(Nat.factorial n : ℂ))*f survivors*
        ((∑ deleted : Fin d → MarkedRawParticle P, (∏ i, ν (deleted i).1)*
          (∏ i, if MarkedRawParticleHits P z hz (deleted i) then (1:ℂ) else 0)*
          g (Fin.addCases survivors deleted))/(Nat.factorial d : ℂ)) := by
      rw [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro deleted _
      field_simp
    _ = _ := by
      rw [markedRawParticle_batch_hit_integral P ν z hz d (fun deleted => g (Fin.addCases survivors deleted))]
      simp only [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro births _
      ring

end ArtinMatthews
