module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The actual valuation-defined S-integers at the prime support of a
nonzero integral denominator form the localization away from it. -/

namespace ArtinMatthews.SIntegerPrincipalization

open NumberField IsDedekindDomain Set
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

abbrev IntegerRing (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  ↥(Set.integer (R := 𝓞 K) (↑S : Set (HeightOneSpectrum (𝓞 K))) K)

theorem denominatorSupport_finite (d : 𝓞 K) (hd : d ≠ 0) :
    {p : HeightOneSpectrum (𝓞 K) | d ∈ p.asIdeal}.Finite := by
  have hi : (Ideal.span {d} : Ideal (𝓞 K)) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hd
  apply ((Ideal.finite_setOfPred_absNorm_le (Ideal.absNorm (Ideal.span {d}))).preimage
    HeightOneSpectrum.asIdeal_injective.injOn).subset
  intro p hp
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hi))
    (Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hp))

def denominatorSupport (d : 𝓞 K) (hd : d ≠ 0) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (denominatorSupport_finite d hd).toFinset

@[simp] theorem mem_denominatorSupport (d : 𝓞 K) (hd : d ≠ 0) (p : HeightOneSpectrum (𝓞 K)) :
    p ∈ denominatorSupport d hd ↔ d ∈ p.asIdeal := Set.Finite.mem_toFinset _

theorem exists_mul_pow_integer (d : 𝓞 K) (hd : d ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ p, p ∈ S ↔ d ∈ p.asIdeal)
    (x : IntegerRing (K := K) S) :
    ∃ (n : ℕ) (a : 𝓞 K), (x : K) * (algebraMap (𝓞 K) K d) ^ n = algebraMap (𝓞 K) K a := by
  by_cases hx : (x : K) = 0
  · exact ⟨0, 0, by simp [hx]⟩
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := (IsFractionRing.injective (𝓞 K) K).ne hd
  let N : ℕ := ∑ p ∈ S, (WithZero.log (p.valuation K (x : K))).toNat
  have hv (p : HeightOneSpectrum (𝓞 K)) :
      p.valuation K ((x : K) * (algebraMap (𝓞 K) K d) ^ N) ≤ 1 := by
    by_cases hp : p ∈ S
    · have hdx : p.valuation K (algebraMap (𝓞 K) K d) ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr hdK
      have hxx : p.valuation K (x : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
      have hdl : WithZero.log (p.valuation K (algebraMap (𝓞 K) K d)) ≤ -1 := by
        have ht := (WithZero.log_lt_log hdx one_ne_zero).mpr
          ((p.valuation_lt_one_iff_mem (K := K) d).mpr ((hS p).mp hp))
        rw [WithZero.log_one] at ht
        omega
      have hn : (WithZero.log (p.valuation K (x : K))).toNat ≤ N :=
        Finset.single_le_sum (f := fun q : HeightOneSpectrum (𝓞 K) =>
          (WithZero.log (q.valuation K (x : K))).toNat) (fun _ _ => Nat.zero_le _) hp
      have hxl : WithZero.log (p.valuation K (x : K)) ≤ (N : ℤ) := by omega
      rw [← WithZero.log_le_log ((Valuation.ne_zero_iff _).mpr (mul_ne_zero hx (pow_ne_zero N hdK)))
        one_ne_zero, map_mul, map_pow, WithZero.log_mul hxx (pow_ne_zero N hdx),
        WithZero.log_pow, WithZero.log_one]
      simp only [nsmul_eq_mul]
      have hm := mul_le_mul_of_nonneg_left hdl (Int.natCast_nonneg N)
      linarith
    · have hvd : p.valuation K (algebraMap (𝓞 K) K d) = 1 :=
        p.valuation_eq_one_iff_notMem.mpr (fun hm => hp ((hS p).mpr hm))
      rw [map_mul, map_pow, hvd, one_pow, mul_one]
      exact x.property p hp
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K _ hv
  exact ⟨N, a, ha.symm⟩

theorem denominator_isUnit (d : 𝓞 K) (hd : d ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ p, p ∈ S ↔ d ∈ p.asIdeal) :
    IsUnit (algebraMap (𝓞 K) (IntegerRing (K := K) S) d) := by
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := (IsFractionRing.injective (𝓞 K) K).ne hd
  let y : IntegerRing (K := K) S := ⟨(algebraMap (𝓞 K) K d)⁻¹, by
    intro p hp
    rw [map_inv₀, p.valuation_eq_one_iff_notMem.mpr (fun hm => hp ((hS p).mpr hm)), inv_one]⟩
  refine ⟨⟨algebraMap (𝓞 K) (IntegerRing (K := K) S) d, y, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    exact mul_inv_cancel₀ hdK
  · apply Subtype.ext
    exact inv_mul_cancel₀ hdK

theorem integerRing_isLocalization_away (d : 𝓞 K) (hd : d ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ p, p ∈ S ↔ d ∈ p.asIdeal) :
    IsLocalization.Away d (IntegerRing (K := K) S) := by
  refine IsLocalization.Away.mk d (denominator_isUnit d hd S hS) ?_ ?_
  · intro x
    obtain ⟨n, a, ha⟩ := exists_mul_pow_integer d hd S hS x
    refine ⟨n, a, ?_⟩
    apply Subtype.ext
    exact ha
  · intro a b hab
    refine ⟨0, ?_⟩
    have h := congrArg (fun x : IntegerRing (K := K) S => (x : K)) hab
    have he : a = b := IsFractionRing.injective (𝓞 K) K h
    simp only [pow_zero, one_mul, he]

theorem integerRing_isDedekindDomain (d : 𝓞 K) (hd : d ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ p, p ∈ S ↔ d ∈ p.asIdeal) :
    IsDedekindDomain (IntegerRing (K := K) S) := by
  let : IsLocalization.Away d (IntegerRing (K := K) S) := integerRing_isLocalization_away d hd S hS
  have hm : Submonoid.powers d ≤ (𝓞 K)⁰ := by
    rintro x ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hd)
  exact IsLocalization.isDedekindDomain (𝓞 K) hm (IntegerRing (K := K) S)

end
end ArtinMatthews.SIntegerPrincipalization
