module

public import ArtinMatthews.KummerPrimitiveNonreal
public import ArtinMatthews.VaryingKummerAnalyticMixedXiZeroStrip


set_option backward.privateInPublic true
@[expose] public section

/-! The actual zero-source reduction for K_q=Q(mu_q,a^(1/q)).
The principal cyclotomic factor is retained. All other sources are
non-real primitive Hecke factors over Q(mu_12q), with explicit q-dependent
conductor bounds. This does not assert the fixed-width zero-free theorem. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain
open scoped NumberField Classical IsMulCommutative
noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem PrimitiveArtinZeroWitness.log_conductor_le {s : ℂ}
    (w : PrimitiveArtinZeroWitness K L s) :
    Real.log (w.conductor.absNorm : ℝ) ≤
      (Module.finrank ℚ K : ℝ) * Real.log (discriminantDegreeModulus K L : ℝ) := by
  have hfpos : 0 < (w.conductor.absNorm : ℝ) := by
    exact_mod_cast (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mpr w.conductor_ne_zero))
  have hN := w.norm_le
  rw [rationalModulusIdeal, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at hN
  have hr : (w.conductor.absNorm : ℝ) ≤
      (discriminantDegreeModulus K L : ℝ) ^ Module.finrank ℚ K := by exact_mod_cast hN
  have hlog := Real.log_le_log hfpos hr
  rwa [Real.log_pow] at hlog

theorem PrimitiveArtinZeroWitness.ne_one {s : ℂ} (w : PrimitiveArtinZeroWitness K L s) : s ≠ 1 := by
  intro he
  exact w.one_ne_zero (he ▸ w.zero)

theorem mixedCompletedDedekindXi_zero_regularized (K : Type) [Field K] [NumberField K]
    {s : ℂ} (hs : mixedCompletedDedekindXi K s = 0) : mixedRegularizedDedekindZeta K s = 0 := by
  simp only [mixedRegularizedDedekindZeta, hs, zero_mul, zero_div]

theorem primeKummer_regularized_zero_sources (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]
    (hq : 2 < q) {s : ℂ} (hs : 0 < s.re)
    (hz : mixedRegularizedDedekindZeta (primeKummerField q a) s = 0) :
    mixedRegularizedDedekindZeta (twelfthCyclotomicField q) s = 0 ∨
      Nonempty (PrimitiveArtinZeroWitness (twelfthCyclotomicField q) (twelfthKummerField q a) s) := by
  let := primeKummerField_isTotallyComplex q a hq
  have htop := ArtinRay.regularizedDedekindZeta_base_zero
    (primeKummerField q a) (twelfthKummerField q a) hs hz
  exact (ArtinRay.regularizedDedekindZeta_zero_sources
    (twelfthCyclotomicField q) (twelfthKummerField q a) hs).mp htop

theorem twelfthKummer_primitive_zero_source_log_conductor
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] (haq : a.natAbs ≤ q) {s : ℂ}
    (w : PrimitiveArtinZeroWitness (twelfthCyclotomicField q) (twelfthKummerField q a) s) :
    Real.log (w.conductor.absNorm : ℝ) ≤
      (12 * q : ℝ) * ((72 * (q : ℝ)^2 + 2) * Real.log (12 * q)) := by
  have hdim : (Module.finrank ℚ (twelfthCyclotomicField q) : ℝ) ≤ (12 * q : ℝ) := by
    rw [finrank_twelfthCyclotomicField]
    exact_mod_cast Nat.totient_le (12 * q)
  have hlog := twelfthKummer_cyclotomic_discriminantDegreeModulus_log_le q a haq
  have hB : 0 ≤ (72 * (q : ℝ)^2 + 2) * Real.log (12 * q) := by
    have hq0 := NeZero.pos q
    have : (1 : ℝ) ≤ 12 * q := by exact_mod_cast (show 1 ≤ 12 * q by omega)
    exact mul_nonneg (by positivity) (Real.log_nonneg this)
  exact w.log_conductor_le.trans
    ((mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hdim hB))

theorem primeKummer_xi_zero_sources (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]
    (hq : 2 < q) (hodd : Odd q) (haq : a.natAbs ≤ q) {s : ℂ} (hs : 0 < s.re)
    (hz : mixedCompletedDedekindXi (primeKummerField q a) s = 0) :
    mixedRegularizedDedekindZeta (twelfthCyclotomicField q) s = 0 ∨
      ∃ w : PrimitiveArtinZeroWitness (twelfthCyclotomicField q) (twelfthKummerField q a) s,
        w.primitiveCharacter.coefficient ≠ w.primitiveCharacter.inverse.coefficient ∧
        (∃ I, (w.primitiveCharacter.coefficient I).im ≠ 0) ∧
        Real.log (w.conductor.absNorm : ℝ) ≤
          (12 * q : ℝ) * ((72 * (q : ℝ)^2 + 2) * Real.log (12 * q)) := by
  rcases primeKummer_regularized_zero_sources q a hq hs
    (mixedCompletedDedekindXi_zero_regularized _ hz) with hbase | hw
  · exact Or.inl hbase
  · obtain ⟨w⟩ := hw
    exact Or.inr ⟨w, (twelfthKummer_primitive_zero_source_nonreal q a hodd w).1,
      (twelfthKummer_primitive_zero_source_nonreal q a hodd w).2,
      twelfthKummer_primitive_zero_source_log_conductor q a haq w⟩


theorem primeKummer_prime_xi_zero_sources (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]
    (hprime : q.Prime) (hq : 2 < q) (haq : a.natAbs ≤ q) {s : ℂ} (hs : 0 < s.re)
    (hz : mixedCompletedDedekindXi (primeKummerField q a) s = 0) :
    mixedRegularizedDedekindZeta (twelfthCyclotomicField q) s = 0 ∨
      ∃ w : PrimitiveArtinZeroWitness (twelfthCyclotomicField q) (twelfthKummerField q a) s,
        w.primitiveCharacter.coefficient ≠ w.primitiveCharacter.inverse.coefficient ∧
        (∃ I, (w.primitiveCharacter.coefficient I).im ≠ 0) ∧
        Real.log (w.conductor.absNorm : ℝ) ≤
          (12 * q : ℝ) * ((72 * (q : ℝ)^2 + 2) * Real.log (12 * q)) :=
  primeKummer_xi_zero_sources q a hq (hprime.odd_of_ne_two (by omega)) haq hs hz

end
end ArtinMatthews.VaryingKummerAnalytic
