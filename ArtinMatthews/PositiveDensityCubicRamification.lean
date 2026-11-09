module

public import ArtinMatthews.PositiveDensityCandidateWeights
public import Mathlib.NumberTheory.NumberField.Discriminant.Different


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed exceptional set in the cubic sieve is the actual finite set
of rational primes ramified in the constructed cubic Kummer field. -/

noncomputable section
namespace ArtinMatthews

open scoped NumberField

def giantCubicRamifiedPrimes (S : Finset ℤ) : Finset ℕ :=
  (NumberField.discr (integerCubicField S)).natAbs.primeFactors

theorem giantCubic_not_mem_ramifiedPrimes_iff (S : Finset ℤ) {p : ℕ} (hp : p.Prime) :
    p ∉ giantCubicRamifiedPrimes S ↔
      Algebra.IsUnramifiedIn (𝓞 (integerCubicField S)) (Ideal.span {(p : ℤ)}) := by
  have hpz : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hD := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero (integerCubicField S))
  rw [← NumberField.not_dvd_discr_iff_isUnramifiedIn (integerCubicField S)
    (𝓞 (integerCubicField S)) hpz]
  simp only [giantCubicRamifiedPrimes, Nat.mem_primeFactors, hp, true_and]
  rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  exact not_congr (and_iff_left hD)

theorem giantCubicSieveSelection_discr_iff {S : Finset ℤ}
    {p : ℕ} [Fact p.Prime] (D : IntegralFrobeniusData (integerCubicField S) p)
    (hp₃ : p % 3 = 1) (ha₀ : ∀ a ∈ S, (a : ZMod p) ≠ 0) :
    giantCubicSieveSelection S (giantCubicRamifiedPrimes S) p ↔
      Algebra.IsUnramifiedIn (𝓞 (integerCubicField S)) (Ideal.span {(p : ℤ)}) ∧
        relativeCubicFrobenius D hp₃ ∈ cubicNonfixingSet S := by
  rw [giantCubicSieveSelection_iff_frobenius _ D hp₃ ha₀,
    giantCubic_not_mem_ramifiedPrimes_iff S (Fact.out : p.Prime)]

def giantCubicFrobeniusSelection (S : Finset ℤ) (p : ℕ) : Prop :=
  ∃ (hp : p.Prime) (hp₃ : p % 3 = 1),
    Algebra.IsUnramifiedIn (𝓞 (integerCubicField S)) (Ideal.span {(p : ℤ)}) ∧
      ∃ D : IntegralFrobeniusData (integerCubicField S) p,
        @relativeCubicFrobenius S p ⟨hp⟩ D hp₃ ∈ cubicNonfixingSet S

theorem giantCubicFrobeniusSelection_iff {S : Finset ℤ} {p : ℕ}
    (hp : p.Prime) (hp₃ : p % 3 = 1) (ha₀ : ∀ a ∈ S, (a : ZMod p) ≠ 0) :
    giantCubicFrobeniusSelection S p ↔
      giantCubicSieveSelection S (giantCubicRamifiedPrimes S) p := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨_hp, _hp₃, hu, D, hD⟩
    exact (giantCubicSieveSelection_discr_iff D hp₃ ha₀).mpr ⟨hu, hD⟩
  · intro hs
    obtain ⟨D⟩ := exists_integralFrobeniusData (integerCubicField S) hp
    obtain ⟨hu, hD⟩ := (giantCubicSieveSelection_discr_iff D hp₃ ha₀).mp hs
    exact ⟨hp, hp₃, hu, D, hD⟩

end ArtinMatthews
