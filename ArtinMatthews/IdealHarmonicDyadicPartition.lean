module

public import ArtinMatthews.IdealHarmonicPrimeDyad
public import ArtinMatthews.PrimeExtractionDyadicPartition


set_option backward.privateInPublic true
@[expose] public section

/-! Dyadic decomposition of the actual reciprocal-prime interval sum.
The shifted logarithm gives the sharp cells (2^k,2^(k+1)]. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealHarmonicPrimeFiber (u v : ℝ) (k : ℕ) : Finset ℕ :=
  ((Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime).filter fun p => Nat.log 2 (p - 1) = k

theorem idealHarmonicPrimeFiber_eq (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (k : ℕ) :
    idealHarmonicPrimeFiber u v k =
      (Ioc ⌊max u ((2 : ℝ)^k)⌋₊ ⌊min v (2*(2 : ℝ)^k)⌋₊).filter Nat.Prime := by
  ext p
  by_cases hp : p.Prime
  · have hp2 : 2 ≤ p := hp.two_le
    have hp1 : p - 1 ≠ 0 := by omega
    have hlog : Nat.log 2 (p - 1) = k ↔ (2^k : ℕ) < p ∧ p ≤ 2*2^k := by
      rw [Nat.log_eq_iff (b := 2) (m := k) (n := p - 1) (Or.inr ⟨by norm_num, hp1⟩)]
      simp only [pow_succ']
      omega
    simp only [idealHarmonicPrimeFiber, mem_filter, mem_Ioc, hp, and_true, hlog]
    rw [Nat.floor_lt hu, Nat.le_floor_iff hv,
      Nat.floor_lt (le_max_of_le_right (by positivity)),
      Nat.le_floor_iff (le_min hv (by positivity))]
    simp only [max_lt_iff, le_min_iff]
    constructor
    · rintro ⟨⟨hpu, hpv⟩, hpk, hkp⟩
      exact ⟨⟨hpu, by exact_mod_cast hpk⟩, hpv, by exact_mod_cast hkp⟩
    · rintro ⟨⟨hpu, hpk⟩, hpv, hkp⟩
      exact ⟨⟨hpu, hpv⟩, by exact_mod_cast hpk, by exact_mod_cast hkp⟩
  · simp only [idealHarmonicPrimeFiber, mem_filter, hp, and_false, false_and]

theorem idealHarmonicPrimeInterval_dyadic {q : ℕ} (χ : DirichletCharacter ℂ q)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    idealHarmonicPrimeInterval χ u v =
      ∑ k ∈ range (Nat.log 2 ⌊v⌋₊ + 1),
        idealHarmonicPrimeInterval χ (max u ((2 : ℝ)^k)) (min v (2*(2 : ℝ)^k)) := by
  have he := sum_fiberwise_of_maps_to
    (s := (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime)
    (t := range (Nat.log 2 ⌊v⌋₊ + 1)) (g := fun p => Nat.log 2 (p - 1))
    (fun p hp => mem_range.mpr (Nat.lt_succ_of_le
      (Nat.log_mono_right (by have hh := (mem_Ioc.mp (mem_filter.mp hp).1).2; omega))))
    (fun p => (p : ℂ)⁻¹*χ (p : ZMod q))
  calc
    _ = ∑ k ∈ range (Nat.log 2 ⌊v⌋₊ + 1),
        ∑ p ∈ idealHarmonicPrimeFiber u v k, (p : ℂ)⁻¹*χ (p : ZMod q) := he.symm
    _ = _ := by
      apply sum_congr rfl
      intro k _
      rw [idealHarmonicPrimeFiber_eq u v hu hv k]
      rfl

end
end ArtinMatthews
