module

public import ArtinMatthews.CubicSieveDivisorCoprimeSums
public import ArtinMatthews.CubicSieveHarmonicFloor


set_option backward.privateInPublic true
@[expose] public section

/-! Evaluation of the coprime harmonic and cardinality terms with their
signed divisor logarithms and explicit floor errors. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveCoprimeDensity (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)

def cubicSieveCoprimeLogMoment (d : ℕ) : ℝ :=
  ∑ T ∈ d.primeFactors.powerset, ((-1 : ℝ) ^ T.card / roughSubsetDivisor T) *
    Real.log (roughSubsetDivisor T : ℝ)

theorem cubicSieve_coprimeDensity_eq_totient {d : ℕ} (hd : d ≠ 0) :
    cubicSieveCoprimeDensity d = (d.totient : ℝ) / d := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors d)
  push_cast at h
  rw [h, ← cubicSieveCoprimeDensity, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hd)]

theorem cubicSieve_coprimeDensity_bounds {d : ℕ} (hd : d ≠ 0) :
    0 ≤ cubicSieveCoprimeDensity d ∧ cubicSieveCoprimeDensity d ≤ 1 := by
  rw [cubicSieve_coprimeDensity_eq_totient hd]
  exact ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hd)).mpr
      (Nat.cast_le.mpr (Nat.totient_le d))⟩

theorem cubicSieve_coprime_card_error {d : ℕ} (hd : d ≠ 0) (M : ℕ) :
    |(((Icc 1 M).filter (fun a => a.Coprime d)).card : ℝ) -
      (M : ℝ) * cubicSieveCoprimeDensity d| ≤ (2 : ℝ) ^ d.primeFactors.card := by
  rw [cubicSieve_coprime_card_eq hd, cubicSieveCoprimeDensity,
    ← cubicSieve_coprime_density_eq, mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _T ∈ d.primeFactors.powerset, (1 : ℝ) := by
      apply sum_le_sum
      intro T _
      rw [show (-1 : ℝ) ^ T.card * ((M / roughSubsetDivisor T : ℕ) : ℝ) -
          (M : ℝ) * ((-1 : ℝ) ^ T.card / roughSubsetDivisor T) =
        (-1 : ℝ) ^ T.card * (((M / roughSubsetDivisor T : ℕ) : ℝ) -
          (M : ℝ) / roughSubsetDivisor T) by ring]
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact cubicSieve_floor_div_error M (roughSubsetDivisor T)
    _ = _ := by simp

theorem cubicSieve_coprime_harmonic_error {d M : ℕ} (hd : d ≠ 0) (hdM : d ≤ M) :
    |(∑ a ∈ (Icc 1 M).filter (fun a => a.Coprime d), (a : ℝ)⁻¹) -
      ((Real.log (M : ℝ) + Real.eulerMascheroniConstant) * cubicSieveCoprimeDensity d -
        cubicSieveCoprimeLogMoment d)| ≤ (2 : ℝ) ^ d.primeFactors.card * (2 / M) := by
  rw [cubicSieve_coprime_harmonic_eq hd, cubicSieveCoprimeDensity,
    ← cubicSieve_coprime_density_eq, cubicSieveCoprimeLogMoment, mul_sum,
    ← sum_sub_distrib, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _T ∈ d.primeFactors.powerset, 2 / (M : ℝ) := by
      apply sum_le_sum
      intro T hT
      let a := roughSubsetDivisor T
      let c := (-1 : ℝ) ^ T.card / a
      have hp (p : ℕ) (hp : p ∈ T) : p.Prime :=
        Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp)
      have ha : 0 < a := roughSubsetDivisor_pos T hp
      have had : a ∣ d := (roughSubsetDivisor_dvd_iff T d hp).mpr
        (fun _ hp => Nat.dvd_of_mem_primeFactors (mem_powerset.mp hT hp))
      have haM := (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) had).trans hdM
      have ha₀ : (0 : ℝ) < a := by exact_mod_cast ha
      change |c * (harmonic (M / a) : ℝ) -
        ((Real.log (M : ℝ) + Real.eulerMascheroniConstant) * c -
          c * Real.log (a : ℝ))| ≤ _
      rw [show c * (harmonic (M / a) : ℝ) -
          ((Real.log (M : ℝ) + Real.eulerMascheroniConstant) * c - c * Real.log (a : ℝ)) =
        c * ((harmonic (M / a) : ℝ) -
          (Real.log (M : ℝ) + Real.eulerMascheroniConstant - Real.log (a : ℝ))) by ring,
        abs_mul]
      have hc : |c| = 1 / (a : ℝ) := by
        simp only [c, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos ha₀]
      rw [hc]
      exact (mul_le_mul_of_nonneg_left (cubicSieve_harmonic_div_error ha haM)
        (one_div_nonneg.mpr ha₀.le)).trans_eq (by field_simp)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_powerset, Nat.cast_pow, Nat.cast_ofNat]

end ArtinMatthews
