module

public import ArtinMatthews.MarkedMinorArcRawMemorySymmetry
public import ArtinMatthews.MarkedMinorArcRawMemoryAnchors


set_option backward.privateInPublic true
@[expose] public section

/-! Actual selected-slot retrieval/creation factorial pairing.  The test
may depend jointly on the retrieved prime and the surviving memory, as
required when an edge's target active label is filled by an old particle.
Every old index and repeated particle value is retained. -/
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Genuine one-index factorial pairing with a coupled retrieved-particle
and surviving-memory test. -/
theorem markedRawMemory_factorial_retrieval_pairing {X : Type*} [Fintype X]
    (μ : X → ℂ) (n : ℕ) (g : (Fin (n+1) → X) → ℂ)
    (hg : MarkedRawTupleSymmetric (n+1) g) (F : X → (Fin n → X) → ℂ) :
    (∑ a : Fin (n+1) → X,((∏ k,μ (a k))/(Nat.factorial (n+1) : ℂ))*g a*
      ∑ i : Fin (n+1),F (a i) (Fin.removeNth i a))=
      ∑ p : X,∑ b : Fin n → X,
        ((μ p*(∏ k,μ (b k)))/(Nat.factorial n : ℂ))*g (Fin.snoc b p)*F p b := by
  classical
  calc
    _ = ∑ a : Fin (n+1) → X,((∏ k,μ (a k))/(Nat.factorial (n+1) : ℂ))*
        ∑ i : Fin (n+1),g (Fin.snoc (Fin.removeNth i a) (a i))*F (a i) (Fin.removeNth i a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [markedRawTupleSymmetric_delete g hg a i]
      ring
    _ = _ := by
      rw [markedRawMemory_factorial_single_delete μ n (fun p b => g (Fin.snoc b p)*F p b)]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro b _
      ring

set_option backward.isDefEq.respectTransparency false in
/-- True old-index promotion has exactly the same prime integration as
source-anchored storage. Any `1/V` promotion factor stays inside the joint
test and therefore becomes that same factor on the reversed store. -/
theorem markedRawEdge_anchor_retrieval_pairing (P : Finset Nat.Primes)
    (ν : P → ℂ) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (n : ℕ)
    (g : (Fin (n+1) → MarkedRawParticle P) → ℂ)
    (hg : MarkedRawTupleSymmetric (n+1) g)
    (F : P → (Fin n → MarkedRawParticle P) → ℂ) :
    (∑ a : Fin (n+1) → MarkedRawParticle P,
      ((∏ k,ν (a k).1)/(Nat.factorial (n+1) : ℂ))*g a*
        ∑ i : Fin (n+1),(if MarkedRawParticleHits P z hz (a i) then (1:ℂ) else 0)*
          F (a i).1 (Fin.removeNth i a))=
      ∑ p : P,∑ b : Fin n → MarkedRawParticle P,
        ((ν p*(∏ k,ν (b k).1))/(Nat.factorial n : ℂ))*
          g (Fin.snoc b (markedRawAnchoredParticle P p z hz))*F p b := by
  classical
  erw [markedRawMemory_factorial_retrieval_pairing (fun a : MarkedRawParticle P => ν a.1) n g hg
    (fun p b => (if MarkedRawParticleHits P z hz p then (1:ℂ) else 0)*F p.1 b),
    Finset.sum_comm]
  conv_rhs => erw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = ((∏ k,ν (b k).1)/(Nat.factorial n : ℂ))*
        ∑ p : MarkedRawParticle P,ν p.1*(if MarkedRawParticleHits P z hz p then (1:ℂ) else 0)*
          (g (Fin.snoc b p)*F p.1 b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by
      rw [markedRawParticle_hit_integral P ν z hz (fun p => g (Fin.snoc b p)*F p.1 b),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      have hp : (markedRawAnchoredParticle P p z hz).1=p := rfl
      rw [hp]
      ring

end ArtinMatthews
