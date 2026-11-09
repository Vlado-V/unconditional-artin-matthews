module

public import ArtinMatthews.CubicSieveRestrictedDensity
public import ArtinMatthews.MarkedProgressionWeightedPolynomial


set_option backward.privateInPublic true
@[expose] public section

/-! Squarefree marking divisors give the exact local factors h_s(p). -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

theorem cubicSieve_markingFactor_eq_prod {d : ℕ} (hd : Squarefree d) (s : ℝ) :
    cubicSieveMarkingFactor d s = ∏ p ∈ d.primeFactors, cubicSieveMarkingPrimeFactor p s := by
  have hprod : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
  have hφ := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors d)
  push_cast at hφ
  rw [hprod, ← prod_mul_distrib] at hφ
  have hφ' : (d.totient : ℝ) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
    apply hφ.trans
    apply prod_congr rfl
    intro p hp
    have hp₀ : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    field_simp
  rw [cubicSieveMarkingFactor, cubicSieve_coprimeEulerFactor_eq_prod,
    ← prod_pow, hφ', ← prod_div_distrib]
  rfl

theorem cubicSieve_restrictedMarking_product {d : ℕ} (hd : Squarefree d) (r : ℕ) (s : ℝ) :
    (∏ p ∈ d.primeFactors, cubicSieveRestrictedMarkingDensity r p s) =
      if d.Coprime r then cubicSieveMarkingFactor d s else 0 := by
  by_cases hc : d.Coprime r
  · rw [ite_eq_left hc, cubicSieve_markingFactor_eq_prod hd s]
    apply prod_congr rfl
    intro p hp
    have hpc : p.Coprime r := hc.of_dvd_left (Nat.dvd_of_mem_primeFactors hp)
    exact ite_eq_right ((Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mp hpc)
  · rw [ite_eq_right hc]
    obtain ⟨p, hp, hpd, hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    exact prod_eq_zero (Nat.mem_primeFactors.mpr ⟨hp, hpd, hd.ne_zero⟩) (ite_eq_left hpr)

theorem cubicSieve_markedWeightedDivisor_restricted_product
    (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P)
    {k : ℕ} {i : MarkedWeightedIndex} (hi : i ∈ markedWeightedIndices P S k) (r : ℕ) (s : ℝ) :
    (∏ p ∈ S ∪ i.2, cubicSieveRestrictedMarkingDensity r p s) =
      if (markedWeightedDivisor S i).Coprime r then
        cubicSieveMarkingFactor (markedWeightedDivisor S i) s else 0 := by
  have hT := (mem_powersetCard.mp (mem_sigma.mp hi).2).1
  have hU (p : ℕ) (hp : p ∈ S ∪ i.2) : p.Prime :=
    hP p ((mem_union.mp hp).elim (fun h => hS h) (fun h => (mem_sdiff.mp (hT h)).1))
  have hsq : Squarefree (markedWeightedDivisor S i) := roughSubsetDivisor_squarefree (S ∪ i.2) hU
  have hpf : (markedWeightedDivisor S i).primeFactors = S ∪ i.2 := Nat.primeFactors_prod hU
  simpa only [hpf] using cubicSieve_restrictedMarking_product hsq r s

end ArtinMatthews
