module

public import ArtinMatthews.MarkedProgressionSmooth


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed-residue CRT and smooth-counting step in paper (3.6).
The residue of u+1 is a unit, while the residue of u need not be a unit.
The represented divisor, progression modulus and fixed modulus all remain
in the exact denominator. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators

theorem giant_fixed_residue_coprime {M a r u : ℕ}
    (ha : a.Coprime M) (hr : r ∣ u+1) (hu : Nat.ModEq M (u+1) a) : r.Coprime M := by
  have hunit : (u+1).Coprime M := by
    rw [Nat.coprime_iff_gcd_eq_one, hu.gcd_eq]
    exact ha
  exact Nat.Coprime.of_dvd_left hr hunit

theorem giant_fixed_residue_shift {M : ℕ} (hM : 0 < M) (a u : ℕ) :
    Nat.ModEq M (u+1) a ↔ Nat.ModEq M u (a+M-1) := by
  have hb : Nat.ModEq M (a+M-1+1) a := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ a+M)]
    simp [Nat.ModEq]
  constructor
  · intro hu
    exact Nat.ModEq.add_right_cancel' 1 (hu.trans hb.symm)
  · intro hu
    exact (hu.add_right 1).trans hb

/-- Simultaneous divisibility and fixed residue give one genuine residue
class; no invertibility of a-1 is required. -/
theorem giant_fixed_residue_divisor_crt {M d r : ℕ} (a : ℕ)
    (hM : 0 < M) (hd : 0 < d) (hr : 0 < r)
    (hdr : d.Coprime r) (hdM : d.Coprime M) (hrM : r.Coprime M) :
    ∃ c < d*r*M, ∀ u : ℕ,
      (d ∣ u ∧ r ∣ u+1 ∧ Nat.ModEq M (u+1) a) ↔ Nat.ModEq (d*r*M) u c := by
  obtain ⟨b, _, hb⟩ := marked_divisor_crt hd hr hdr
  have hpair : (d*r).Coprime M := Nat.coprime_mul_iff_left.mpr ⟨hdM,hrM⟩
  let c := Nat.chineseRemainder hpair b (a+M-1)
  refine ⟨c.val, Nat.chineseRemainder_lt_mul hpair b (a+M-1)
    (Nat.mul_pos hd hr).ne' hM.ne', ?_⟩
  intro u
  constructor
  · rintro ⟨hdu,hru,huM⟩
    exact Nat.chineseRemainder_modEq_unique hpair ((hb u).mp ⟨hdu,hru⟩)
      ((giant_fixed_residue_shift hM a u).mp huM)
  · intro hu
    have hs := (Nat.modEq_and_modEq_iff_modEq_mul hpair).mpr hu
    have hdiv := (hb u).mpr (hs.1.trans c.property.1)
    exact ⟨hdiv.1,hdiv.2,(giant_fixed_residue_shift hM a u).mpr (hs.2.trans c.property.2)⟩

theorem giant_fixed_residue_divisor_interval_error (lo hi M a d r : ℕ)
    (hlo : lo ≤ hi) (hM : 0 < M) (hd : 0 < d) (hr : 0 < r)
    (hdr : d.Coprime r) (hdM : d.Coprime M) (hrM : r.Coprime M) :
    |(((Finset.Ioc lo hi).filter
      (fun u => d ∣ u ∧ r ∣ u+1 ∧ Nat.ModEq M (u+1) a)).card : ℝ) -
      ((hi : ℝ)-lo)/(d*r*M : ℕ)| ≤ 1 := by
  classical
  obtain ⟨c, _, hc⟩ := giant_fixed_residue_divisor_crt a hM hd hr hdr hdM hrM
  simpa only [hc] using marked_interval_residue_error lo hi (d*r*M) c hlo
    (Nat.mul_pos (Nat.mul_pos hd hr) hM)

/-- The only empty cases are kept as their original local coprimality
conditions, not discarded from the progression family. -/
theorem giant_fixed_residue_divisor_impossible {M a d r u : ℕ}
    (ha : a.Coprime M) (hbad : ¬(d.Coprime r ∧ r.Coprime M)) :
    ¬(d ∣ u ∧ r ∣ u+1 ∧ Nat.ModEq M (u+1) a) := by
  rintro ⟨hdu,hru,huM⟩
  exact hbad ⟨marked_divisor_coprime hdu hru,giant_fixed_residue_coprime ha hru huM⟩

/-- The actual smooth count required for every retained represented divisor
in (3.6), uniformly in d,r and in the possibly nonunit residue a-1. -/
theorem giant_fixed_residue_divisor_smooth_error (M a d r : ℕ)
    (hM : 0 < M) (hd : 0 < d) (hr : 0 < r) (ha : a.Coprime M) (hdM : d.Coprime M)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0) :
    |(∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter
        (fun u => d ∣ u ∧ r ∣ u+1 ∧ Nat.ModEq M (u+1) a), f u) -
      (if d.Coprime r ∧ r.Coprime M then
        (∫ t in Set.Ioc 0 T, f t)/(d*r*M : ℕ) else 0)| ≤
      3 * ∫ t in Set.Ioc 0 T, |deriv f t| := by
  classical
  by_cases hcop : d.Coprime r ∧ r.Coprime M
  · obtain ⟨c, _, hc⟩ := giant_fixed_residue_divisor_crt a hM hd hr hcop.1 hdM hcop.2
    have h := marked_smooth_sum_error
      (fun u => if d ∣ u ∧ r ∣ u+1 ∧ Nat.ModEq M (u+1) a then (1 : ℝ) else 0) f
      (ρ := 1/(d*r*M : ℕ)) (E := 3) hT hf hderiv hfT (by
        intro t ht
        have he := marked_residue_prefix_error (d*r*M) c
          (Nat.mul_pos (Nat.mul_pos hd hr) hM) ht.1.le
        simpa only [hc, div_eq_mul_inv, one_mul, mul_one, mul_comm] using he)
    rw [ite_eq_left hcop]
    simpa only [Finset.sum_filter, mul_ite, mul_one, mul_zero,
      div_eq_mul_inv, one_mul, mul_comm] using h
  · have hzero : (Finset.Icc 0 ⌊T⌋₊).filter
        (fun u => d ∣ u ∧ r ∣ u+1 ∧ Nat.ModEq M (u+1) a) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      exact fun _ _ => giant_fixed_residue_divisor_impossible ha hcop
    rw [hzero, Finset.sum_empty, ite_eq_right hcop]
    have hi : 0 ≤ ∫ t in Set.Ioc 0 T, |deriv f t| := integral_nonneg (fun t => abs_nonneg _)
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hi

end ArtinMatthews
