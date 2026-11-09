module

public import ArtinMatthews.ProbeIdealPrimeUniformizer
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization


set_option backward.privateInPublic true
@[expose] public section

/-! Actual one-prime pole ideals and nonintegral field traces. These
arithmetic lemmas give nontriviality of the standard local character,+without assuming a local character or a principal prime ideal. -/
namespace ArtinMatthews.StandardAdelic

open NumberField IsDedekindDomain FractionalIdeal
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def poleIdeal (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) : FractionalIdeal (𝓞 K)⁰ K :=
  ((P.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n)⁻¹

theorem poleIdeal_ne_zero (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) : poleIdeal K P n ≠ 0 :=
  inv_ne_zero (pow_ne_zero n (FractionalIdeal.coeIdeal_ne_zero.mpr P.ne_bot))

theorem poleIdeal_count (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    FractionalIdeal.count K P (poleIdeal K P n) = -(n : ℤ) := by
  rw [poleIdeal, FractionalIdeal.count_inv, FractionalIdeal.count_pow_self]

theorem trace_integral_le_codifferent (I : FractionalIdeal (𝓞 K)⁰ K)
    (hI : ∀ x ∈ I, Algebra.trace ℚ K x ∈ (algebraMap ℤ ℚ).range) :
    I ≤ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  intro x hx
  rw [FractionalIdeal.mem_dual one_ne_zero]
  intro y hy
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp hy
  have hxa : x * (algebraMap (𝓞 K) K a) ∈ I.val := by
    simpa only [Algebra.smul_def, mul_comm] using I.val.smul_mem a hx
  simpa only [Algebra.traceForm_apply] using hI _ hxa

theorem exists_nonintegral_trace_in_poleIdeal (P : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (hn : -(n : ℤ) < FractionalIdeal.count K P
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))) :
    ∃ q ∈ poleIdeal K P n, Algebra.trace ℚ K q ∉ (algebraMap ℤ ℚ).range := by
  by_contra h
  have ht : ∀ q ∈ poleIdeal K P n, Algebra.trace ℚ K q ∈ (algebraMap ℤ ℚ).range := by
    simpa only [not_exists, not_and, not_not] using h
  have hle := trace_integral_le_codifferent K _ ht
  have hc := FractionalIdeal.count_mono K P (poleIdeal_ne_zero K P n) hle
  rw [poleIdeal_count] at hc
  exact (not_le_of_gt hn) hc

theorem exists_nonintegral_trace_one_prime (P : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℕ, ∃ q ∈ poleIdeal K P n, Algebra.trace ℚ K q ∉ (algebraMap ℤ ℚ).range := by
  let c := FractionalIdeal.count K P (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))
  have hc : -(c.natAbs : ℤ) ≤ c := by simpa only [Int.abs_eq_natAbs] using neg_abs_le c
  refine ⟨c.natAbs+1, exists_nonintegral_trace_in_poleIdeal K P _ ?_⟩
  change -((c.natAbs+1 : ℕ) : ℤ) < c
  omega

theorem poleIdeal_mul_integer (P : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (q : K) (hq : q ∈ poleIdeal K P n) (a : 𝓞 K) (ha : a ∈ P.asIdeal ^ n) :
    ∃ b : 𝓞 K, (b : K) = q * (a : K) := by
  have hPow : ((P.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n) ≠ 0 :=
    pow_ne_zero n (FractionalIdeal.coeIdeal_ne_zero.mpr P.ne_bot)
  have ha' : (a : K) ∈ (P.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n := by
    rw [← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ ha
  exact (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp ((FractionalIdeal.mem_inv_iff hPow).mp hq _ ha')

theorem poleIdeal_valuation_outside (P : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (q : K) (hq : q ∈ poleIdeal K P n) (w : HeightOneSpectrum (𝓞 K)) (hw : w ≠ P) :
    w.valuation K q ≤ 1 := by
  have hnot : ¬ P.asIdeal ≤ w.asIdeal := by
    intro hle
    have he := (P.isPrime.isMaximal P.ne_bot).eq_of_le w.isPrime.ne_top hle
    exact hw (HeightOneSpectrum.ext he.symm)
  have hex : ∃ a : 𝓞 K, a ∈ P.asIdeal ∧ a ∉ w.asIdeal := by
    by_contra hn
    apply hnot
    intro a ha
    by_contra haw
    exact hn ⟨a,ha,haw⟩
  obtain ⟨a, ha, haw⟩ := hex
  obtain ⟨b, hb⟩ := poleIdeal_mul_integer K P n q hq (a^n) (Ideal.pow_mem_pow ha n)
  have hval : w.valuation K (q * ((a : K)^n)) ≤ 1 := by
    rw [← map_pow (algebraMap (𝓞 K) K), ← hb, w.valuation_of_algebraMap]
    exact w.intValuation_le_one b
  have haVal : w.valuation K (a : K) = 1 := (w.valuation_eq_one_iff_notMem (K := K)).mpr haw
  simpa only [map_mul, map_pow, haVal, one_pow, mul_one] using hval

theorem poleIdeal_uniformizer_integral (P : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (q : K) (hq : q ∈ poleIdeal K P n) :
    P.valuation K (q * (algebraMap (𝓞 K) K (probeIdealUniformizer P))^n) ≤ 1 := by
  obtain ⟨b, hb⟩ := poleIdeal_mul_integer K P n q hq (probeIdealUniformizer P ^ n)
    (probeIdealUniformizer_pow_mem P n)
  rw [← map_pow (algebraMap (𝓞 K) K), ← hb, P.valuation_of_algebraMap]
  exact P.intValuation_le_one b

end
end ArtinMatthews.StandardAdelic
