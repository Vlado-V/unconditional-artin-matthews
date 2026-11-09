module

public import ArtinMatthews.VaryingKummerAnalyticDedekindNonvanishingLocal


set_option backward.privateInPublic true
@[expose] public section

/-! Degree-uniform bounds for the actual prime-ideal norm fibers. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField Finset UniqueFactorizationMonoid
open OAI.PrimeDegreePackets
open scoped NumberField BigOperators

/-- Every prime ideal above a rational prime has norm at least that prime. -/
theorem idealsOverPrime_norm_ge_prime (K : Type*) [Field K] [NumberField K]
    {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P ∈ idealsOverPrime K p) :
    p ≤ Ideal.absNorm P := by
  have hfac : P ∈ normalizedFactors (Ideal.span {(p : 𝓞 K)}) :=
    Multiset.mem_toFinset.mp hP
  exact (ideal_factor_prime_power K hp (Ideal.absNorm_span_natCast p) hfac).2

/-- Actual prime-ideal norm powers are controlled by the degree times the
corresponding rational-prime norm power. -/
theorem prime_ideal_norm_series_le (K : Type*) [Field K] [NumberField K]
    (p : Nat.Primes) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∑ P : idealsOverPrime K p, (Ideal.absNorm P.val : ℝ) ^ (-σ)) ≤
      (Module.finrank ℚ K : ℝ) * (p : ℝ) ^ (-σ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hcard : (idealsOverPrime K p).card ≤ Module.finrank ℚ K := by
    simpa only [NumberField.RingOfIntegers.rank K] using idealsOverPrime_card_le K p.property
  calc
    _ ≤ ∑ _P : idealsOverPrime K p, (p : ℝ) ^ (-σ) := by
      apply Finset.sum_le_sum
      intro P _
      exact Real.rpow_le_rpow_of_nonpos hp
        (by exact_mod_cast idealsOverPrime_norm_ge_prime K p.property P.property)
        (neg_nonpos.mpr hσ)
    _ = ((idealsOverPrime K p).card : ℝ) * (p : ℝ) ^ (-σ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (Real.rpow_nonneg hp.le _)

theorem prime_rpow_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ)) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact h.subtype Nat.Prime

end
end ArtinMatthews.VaryingKummerAnalytic
