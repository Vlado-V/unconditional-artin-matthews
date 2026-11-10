module

public import ArtinMatthews.Definitions
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import ArtinMatthews.NegativeThreeSquare
public import ArtinMatthews.PrimitiveArithmetic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

theorem legendre_neg_three_eq_at_three {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    legendreSym p (-3) = legendreSym 3 p := by
  have hp : p.Prime := Fact.out
  have hpodd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have hqr : legendreSym p 3 = (-1 : ℤ) ^ (p / 2) * legendreSym 3 p := by
    simpa using (legendreSym.quadratic_reciprocity' (p := 3) (q := p)
      (by decide : (3 : ℕ) ≠ 2) hp2)
  have hs : ((-1 : ℤ) ^ (p / 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  calc
    legendreSym p (-3) = legendreSym p (-1) * legendreSym p 3 := by
      rw [← legendreSym.mul]
      norm_num
    _ = ((-1 : ℤ) ^ (p / 2)) ^ 2 * legendreSym 3 p := by
      rw [legendreSym.at_neg_one hp2, ZMod.χ₄_eq_neg_one_pow hpodd, hqr]
      ring
    _ = legendreSym 3 p := by rw [hs, one_mul]

theorem one_mod_three_of_legendre_three_eq_one {p : ℕ}
    (h : legendreSym 3 p = 1) : p % 3 = 1 := by
  have hmod := legendreSym.mod 3 (p : ℤ)
  rw [h] at hmod
  have hc : ((p : ℤ) % (3 : ℕ)) = (p % 3 : ℕ) := by omega
  rw [hc] at hmod
  have hr := Nat.mod_lt p (by decide : 0 < 3)
  interval_cases hh : p % 3
  · norm_num [legendreSym, quadraticChar] at hmod
  · rfl
  · have hn : ¬ IsSquare (2 : ZMod 3) := by decide
    have hv : legendreSym 3 (2 : ℤ) = -1 := (legendreSym.eq_neg_one_iff 3).mpr hn
    norm_num [hv] at hmod

/-- An even product of primitive roots has Legendre symbol one at an odd prime. -/
theorem even_product_primitive_legendre {p : ℕ} [Fact p.Prime] {T : Finset ℤ}
    (hp2 : p ≠ 2) (hT : Even T.card)
    (hprim : ∀ a ∈ T, IsPrimitiveRootMod p a) :
    legendreSym p (∏ a ∈ T, a) = 1 := by
  calc
    legendreSym p (∏ a ∈ T, a) = ∏ a ∈ T, legendreSym p a := by
      exact map_prod (legendreSym.hom p) _ _
    _ = ∏ _a ∈ T, (-1 : ℤ) := by
      apply Finset.prod_congr rfl
      intro a ha
      exact primitive_legendre_eq_neg_one hp2 (hprim a ha)
    _ = (-1 : ℤ) ^ T.card := by simp
    _ = 1 := hT.neg_one_pow

/-- Under obstruction B, simultaneous primitive-root primes belong to {2, 3}. -/
theorem obstructionB_prime_eq_two_or_three {S : Finset ℤ} (hB : ObstructionB S)
    {p : ℕ} (hp : p ∈ SimultaneousPrimitivePrimes S) : p = 2 ∨ p = 3 := by
  rcases hp with ⟨hprime, hprim⟩
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  by_cases hp3 : p = 3
  · exact Or.inr hp3
  let : Fact p.Prime := ⟨hprime⟩
  rcases hB.1 with ⟨T, hTS, hEven, hSquare⟩
  have hTP : ∀ a ∈ T, IsPrimitiveRootMod p a := fun a ha => hprim a (hTS ha)
  have hz0 : ((∏ a ∈ T, a : ℤ) : ZMod p) ≠ 0 := by
    simp only [Int.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun a ha => (hTP a ha).1)
  have hleg : legendreSym p (-3) = 1 := by
    rw [← negativeThreeRationalSquare_legendre hp3 hSquare hz0]
    exact even_product_primitive_legendre hp2 hEven hTP
  have hpmod : p % 3 = 1 := by
    apply one_mod_three_of_legendre_three_eq_one
    rwa [← legendre_neg_three_eq_at_three hp2]
  rcases hB.2 p hprime hpmod with ⟨a, ha, hcube⟩
  exact False.elim (primitive_not_cube hprime hpmod (hprim a ha) hcube)

/-- In fact the prime 3 is excluded by the negative-three product identity. -/
theorem obstructionB_prime_eq_two {S : Finset ℤ} (hB : ObstructionB S)
    {p : ℕ} (hp : p ∈ SimultaneousPrimitivePrimes S) : p = 2 := by
  rcases obstructionB_prime_eq_two_or_three hB hp with h | h
  · exact h
  · subst p
    rcases hB.1 with ⟨T, hTS, _hEven, hSquare⟩
    have hz0 : ((∏ a ∈ T, a : ℤ) : ZMod 3) ≠ 0 := by
      simp only [Int.cast_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun a ha => (hp.2 a (hTS ha)).1)
    apply False.elim
    exact hz0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      (negativeThreeRationalSquare_three_dvd hSquare))

/-- The second Matthews obstruction allows only finitely many simultaneous primes. -/
theorem obstructionB_finite {S : Finset ℤ} (hB : ObstructionB S) :
    (SimultaneousPrimitivePrimes S).Finite := by
  apply (Set.finite_singleton 2).subset
  intro p hp
  simpa only [Set.mem_singleton_iff] using obstructionB_prime_eq_two hB hp

end ArtinMatthews
