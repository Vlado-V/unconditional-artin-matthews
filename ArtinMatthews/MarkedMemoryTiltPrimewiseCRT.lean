module

public import ArtinMatthews.MarkedMemoryTiltPrimewiseRoot


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite squarefree SL₂/independent-line factorization of the
literal primewise path tests. This is a finite uniform residue-root model;
it makes no archimedean root-replacement claim for the full band modulus.
The chronological lifespan/history correspondence is also separate. -/
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

abbrev markedMemoryCRTPrime {S : ℕ} (p : S.primeFactors) : Nat.Primes :=
  ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩

def markedMemoryCRTLineTest {S N : ℕ} (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ j, IsCoprime (z j).1 (z j).2)
    (A : S.primeFactors → Finset (Fin (N+1))) (p : S.primeFactors)
    (ℓ : MarkedRawPrimeLine (markedMemoryCRTPrime p)) : ℂ :=
  (((∏ j ∈ A p, (markedLineHit (markedMemoryPositionLines (markedMemoryCRTPrime p) z hz) j ℓ : ℝ)) *
    ∏ j ∈ Finset.univ \ A p,
      (1-markedMemoryEta q N j * markedLineHit (markedMemoryPositionLines (markedMemoryCRTPrime p) z hz) j ℓ)) : ℝ)

/-- The complete finite path-test average factors exactly into the actual
primewise averages, including each possible incompatible-active zero. -/
theorem markedMemoryCRT_projective_factorization {S N : ℕ} [NeZero S]
    (hS : Squarefree S) (q : ℝ) (z : Fin (N+1) → ℤ × ℤ)
    (hz : ∀ j, IsCoprime (z j).1 (z j).2)
    (A : S.primeFactors → Finset (Fin (N+1))) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℂ)⁻¹ *
      (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
        ∏ p : S.primeFactors, markedMemoryCRTLineTest q z hz A p (markedRootKernelTuple hS g p)) =
      ∏ p : S.primeFactors, (markedMemoryProjectiveFactor (markedMemoryCRTPrime p) q z hz (A p) : ℂ) := by
  rw [marked_squarefree_root_kernel_tuple_average hS
    (fun ℓ => ∏ p : S.primeFactors, markedMemoryCRTLineTest q z hz A p (ℓ p))]
  rw [← Fintype.prod_sum (markedMemoryCRTLineTest q z hz A)]
  push_cast
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [markedMemoryProjectiveFactor, markedMemoryPrimeFactor_complex, markedMemoryPrimeLine_card]
  rw [Complex.ofReal_sum]
  simp only [markedMemoryCRTLineTest, Nat.cast_add, Nat.cast_one]

/-- The same average expressed as literal first-row divisibility tests
of the actual CRT-reduced root matrices. -/
theorem markedMemoryCRT_root_factorization {S N : ℕ} [NeZero S]
    (hS : Squarefree S) (q : ℝ) (z : Fin (N+1) → ℤ × ℤ)
    (hz : ∀ j, IsCoprime (z j).1 (z j).2)
    (A : S.primeFactors → Finset (Fin (N+1))) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℂ)⁻¹ *
      (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S), ∏ p : S.primeFactors,
        ((((∏ j ∈ A p, markedMemoryRootHit (markedMemoryCRTPrime p) (markedSquarefreeRootCRT hS g p) (z j)) *
          ∏ j ∈ Finset.univ \ A p,
            (1-markedMemoryEta q N j * markedMemoryRootHit (markedMemoryCRTPrime p)
              (markedSquarefreeRootCRT hS g p) (z j))) : ℝ) : ℂ)) =
      ∏ p : S.primeFactors, (markedMemoryProjectiveFactor (markedMemoryCRTPrime p) q z hz (A p) : ℂ) := by
  calc
    _ = (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℂ)⁻¹ *
        (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
          ∏ p : S.primeFactors, markedMemoryCRTLineTest q z hz A p (markedRootKernelTuple hS g p)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.prod_congr rfl
      intro p _
      simp only [markedMemoryCRTLineTest, markedRootKernelTuple,
        markedMemoryRootHit_eq (markedMemoryCRTPrime p) _ z hz]
    _ = _ := markedMemoryCRT_projective_factorization hS q z hz A

/-- Exact root factorization for the active sets computed from the
original path of typed labels, without a supplied active-set identity. -/
theorem markedMemoryCRT_root_factorization_slots {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M S N : ℕ} [NeZero S]
    (hS : Squarefree S) (slots : Fin (N+1) → MarkedRawActive P M)
    (q : ℝ) (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ j, IsCoprime (z j).1 (z j).2) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℂ)⁻¹ *
      (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S), ∏ p : S.primeFactors,
        ((((∏ j ∈ markedMemoryActiveVisits slots (markedMemoryCRTPrime p),
            markedMemoryRootHit (markedMemoryCRTPrime p) (markedSquarefreeRootCRT hS g p) (z j)) *
          ∏ j ∈ Finset.univ \ markedMemoryActiveVisits slots (markedMemoryCRTPrime p),
            (1-markedMemoryEta q N j * markedMemoryRootHit (markedMemoryCRTPrime p)
              (markedSquarefreeRootCRT hS g p) (z j))) : ℝ) : ℂ)) =
      ∏ p : S.primeFactors, (markedMemoryProjectiveFactor (markedMemoryCRTPrime p) q z hz
        (markedMemoryActiveVisits slots (markedMemoryCRTPrime p)) : ℂ) :=
  markedMemoryCRT_root_factorization hS q z hz _

/-- The actual singleton baselines are extracted once per prime. This
does not identify the original physical mass with the tilted raw mass. -/
theorem markedMemoryCRT_baseline_extraction {S N : ℕ} (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ j, IsCoprime (z j).1 (z j).2)
    (A : S.primeFactors → Finset (Fin (N+1)))
    (hb : ∀ p : S.primeFactors, markedMemoryBaseline q N (markedMemoryCRTPrime p) ≠ 0) :
    (∏ p : S.primeFactors, markedMemoryProjectiveFactor (markedMemoryCRTPrime p) q z hz (A p)) =
      (∏ p : S.primeFactors, markedMemoryBaseline q N (markedMemoryCRTPrime p)) *
        ∏ p : S.primeFactors, (markedMemoryProjectiveFactor (markedMemoryCRTPrime p) q z hz (A p) /
          markedMemoryBaseline q N (markedMemoryCRTPrime p)) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  field_simp [hb p]

end ArtinMatthews
