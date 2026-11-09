module

public import ArtinMatthews.PrimitiveArithmetic


set_option backward.privateInPublic true
@[expose] public section

/-!
# The odd square-product obstruction

This module proves the algebraic contradiction behind condition (A).  It does
not use the analytic estimates in the paper.
-/

namespace ArtinMatthews

/-- An integer that is a rational square is already an integer square. -/
theorem RationalSquare.isSquare {z : ℤ} (hz : RationalSquare z) : IsSquare z := by
  rcases hz with ⟨q, _, hq⟩
  apply Rat.isSquare_intCast_iff.mp
  exact ⟨q, by simpa only [pow_two] using hq.symm⟩

/-- An odd product of quadratic nonresidues cannot be a rational square. -/
theorem odd_nonresidue_product_not_rationalSquare {p : ℕ} [Fact p.Prime]
    {T : Finset ℤ} (hodd : Odd T.card)
    (hneg : ∀ a ∈ T, legendreSym p a = -1) :
    ¬ RationalSquare (∏ a ∈ T, a) := by
  intro hsquare
  have hproduct : legendreSym p (∏ a ∈ T, a) = -1 := by
    calc
      legendreSym p (∏ a ∈ T, a) = ∏ a ∈ T, legendreSym p a := by
        exact map_prod (legendreSym.hom p) (fun a : ℤ => a) T
      _ = ∏ _a ∈ T, (-1 : ℤ) := Finset.prod_congr rfl hneg
      _ = (-1 : ℤ) ^ T.card := by simp
      _ = -1 := hodd.neg_one_pow
  rcases hsquare.isSquare with ⟨b, hb⟩
  rw [hb, legendreSym.mul] at hproduct
  nlinarith [sq_nonneg (legendreSym p b)]

/-- Under obstruction (A), a simultaneous primitive-root prime can only be 2. -/
theorem obstructionA_prime_eq_two {S : Finset ℤ} (hA : ObstructionA S)
    {p : ℕ} (hp : p ∈ SimultaneousPrimitivePrimes S) : p = 2 := by
  by_contra hp2
  obtain ⟨T, hTS, hodd, hsquare⟩ := hA
  let : Fact p.Prime := ⟨hp.1⟩
  apply odd_nonresidue_product_not_rationalSquare (p := p) hodd _ hsquare
  intro a ha
  exact primitive_legendre_eq_neg_one hp2 (hp.2 a (hTS ha))

/-- The exceptional set in obstruction (A) is contained in the singleton {2}. -/
theorem obstructionA_subset_singleton {S : Finset ℤ} (hA : ObstructionA S) :
    SimultaneousPrimitivePrimes S ⊆ {2} := by
  intro p hp
  exact Set.mem_singleton_iff.mpr (obstructionA_prime_eq_two hA hp)

/-- The finiteness implication of Theorem 1.1 for obstruction (A). -/
theorem obstructionA_finite {S : Finset ℤ} (hA : ObstructionA S) :
    (SimultaneousPrimitivePrimes S).Finite :=
  (Set.finite_singleton 2).subset (obstructionA_subset_singleton hA)

end ArtinMatthews
