module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine integral local uniformizers for arbitrary height-one primes.
No principal-ideal assertion is made about the chosen element. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open IsDedekindDomain WithZero
noncomputable section

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

def probeIdealUniformizer (P : HeightOneSpectrum R) : R :=
  P.intValuation_exists_uniformizer.choose

theorem probeIdealUniformizer_valuation (P : HeightOneSpectrum R) :
    P.intValuation (probeIdealUniformizer P) = WithZero.exp (-1 : ℤ) :=
  P.intValuation_exists_uniformizer.choose_spec

theorem probeIdealUniformizer_ne_zero (P : HeightOneSpectrum R) :
    probeIdealUniformizer P ≠ 0 := by
  intro h
  have he := probeIdealUniformizer_valuation P
  rw [h, map_zero] at he
  exact WithZero.exp_ne_zero he.symm

theorem probeIdealUniformizer_pow_valuation (P : HeightOneSpectrum R) (k : ℕ) :
    P.intValuation (probeIdealUniformizer P ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [map_pow, probeIdealUniformizer_valuation, ← WithZero.exp_nsmul]
  congr 1
  simp

theorem probeIdealUniformizer_mem (P : HeightOneSpectrum R) :
    probeIdealUniformizer P ∈ P.asIdeal := by
  rw [← pow_one P.asIdeal, ← P.intValuation_le_pow_iff_mem,
    probeIdealUniformizer_valuation]
  norm_num

theorem probeIdealUniformizer_notMem_sq (P : HeightOneSpectrum R) :
    probeIdealUniformizer P ∉ P.asIdeal ^ 2 := by
  rw [← P.intValuation_le_pow_iff_mem, probeIdealUniformizer_valuation,
    WithZero.exp_le_exp]
  norm_num

theorem probeIdealUniformizer_pow_mul_mem_iff (P : HeightOneSpectrum R)
    (n k : ℕ) (x : R) :
    probeIdealUniformizer P ^ k * x ∈ P.asIdeal ^ (n + k) ↔ x ∈ P.asIdeal ^ n := by
  by_cases hx : x = 0
  · simp [hx]
  rw [← P.intValuation_le_pow_iff_mem, ← P.intValuation_le_pow_iff_mem,
    map_mul, probeIdealUniformizer_pow_valuation, P.intValuation_if_neg hx,
    ← WithZero.exp_add, WithZero.exp_le_exp, WithZero.exp_le_exp]
  simp only [Nat.cast_add]
  omega

theorem probeIdealUniformizer_pow_mem (P : HeightOneSpectrum R) (k : ℕ) :
    probeIdealUniformizer P ^ k ∈ P.asIdeal ^ k := by
  have he := (probeIdealUniformizer_pow_mul_mem_iff P 0 k (1 : R)).mpr
    (by simp : (1 : R) ∈ P.asIdeal ^ 0)
  simpa only [Nat.zero_add, mul_one] using he

theorem probeIdealUniformizer_approx (P : HeightOneSpectrum R) (n k : ℕ)
    (x : R) (hx : x ∈ P.asIdeal ^ k) :
    ∃ y : R, x - probeIdealUniformizer P ^ k * y ∈ P.asIdeal ^ (n + k) := by
  have hv : P.intValuation x ≤ P.intValuation (probeIdealUniformizer P ^ k) := by
    rw [probeIdealUniformizer_pow_valuation]
    exact (P.intValuation_le_pow_iff_mem x k).mpr hx
  obtain ⟨y, hy⟩ := P.exists_intValuation_mul_sub_lt hv
    (Multiplicative.ofAdd (-((n + k : ℕ) : ℤ)))
  refine ⟨y, ?_⟩
  apply (P.intValuation_le_pow_iff_mem _ (n + k)).mp
  have he : P.intValuation (x - y * probeIdealUniformizer P ^ k) ≤
      WithZero.exp (-((n + k : ℕ) : ℤ)) := le_of_lt hy
  simpa only [mul_comm y] using he

end

end ArtinMatthews.VaryingKummerAnalytic
