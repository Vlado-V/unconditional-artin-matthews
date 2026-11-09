module

public import ArtinMatthews.ProbeLocalSurvivorIndex
public import ArtinMatthews.ProbeIdealLocalCoefficient


set_option backward.privateInPublic true
@[expose] public section

/-! An explicit, injective enumeration of every possible nonzero local
index at j=0.  Coverage follows from the actual finite coefficient table. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probeIdealCoefficient_support (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (i : ProbeLocalRawIndex)
    (hi : probeIdealLocalCoefficient K P χ (probeLocalIndexDegree i)
      i.2.2.1 (6 * i.2.2.2) ≠ 0) : i ∈ Set.range probeLocalSurvivorIndex := by
  rcases i with ⟨e, l, k, r⟩
  cases e with
  | false =>
    simp only [probeLocalIndexDegree, Bool.false_eq_true, ite_false, zero_add] at hi
    change probeIdealLocalCoefficient K P χ (3 * l) k (6 * r) ≠ 0 at hi
    by_cases hl : l = 0
    · subst l
      cases k with
      | zero => exact ⟨.inl r, rfl⟩
      | succ k =>
        have hr : r = 0 := by
          by_contra hn
          apply hi
          simp only [mul_zero, probeIdealLocalCoefficient_zero_succ K P,
            ite_eq_right hn]
        subst r
        exact ⟨.inr (.inl k), rfl⟩
    · by_cases heven : l % 2 = 0
      · let d := l / 2 - 1
        have hld : l = 2 * (d + 1) := by dsimp [d]; omega
        have ht : 3 * l = (6 * d + 5) + 1 := by omega
        rw [ht] at hi
        cases k with
        | zero =>
          change probeIdealLocalCZero K P χ (6 * d + 5) (6 * r) ≠ 0 at hi
          have hdr : d < r := by
            by_contra hn
            exact hi (by rw [probeIdealLocalCZero_zero_class K P χ hχ, ite_eq_right hn])
          refine ⟨.inr (.inr (.inl (d, r - (d + 1)))), ?_⟩
          simp only [probeLocalSurvivorIndex, hld]
          have hr : d + 1 + (r - (d + 1)) = r := by omega
          rw [hr]
        | succ k =>
          cases k with
          | zero =>
            change probeIdealLocalCOne K P χ (6 * d + 5) (6 * r) ≠ 0 at hi
            have hr : r = d + 1 := by
              by_contra hn
              exact hi (by rw [probeIdealLocalCOne_zero_class K P χ hχ hminus, ite_eq_right hn])
            refine ⟨.inr (.inr (.inr (.inl d))), ?_⟩
            simp only [probeLocalSurvivorIndex, hld, hr]
          | succ k => exact False.elim (hi (probeIdealLocalCoefficient_higher K P χ _ k _))
      · let d := l / 2
        have ht : 3 * l = 6 * d + 3 := by dsimp [d]; omega
        exact False.elim (hi (by rw [ht]; exact probeIdealLocalCoefficient_zero_odd K P χ hχ hminus d k r))
  | true =>
    change probeIdealLocalCoefficient K P χ (1 + 3 * l) k (6 * r) ≠ 0 at hi
    by_cases heven : l % 2 = 0
    · let d := l / 2
      have hld : l = 2 * d := by dsimp [d]; omega
      have ht : 1 + 3 * l = 6 * d + 1 := by omega
      rw [ht] at hi
      cases k with
      | zero =>
        change probeIdealLocalCZero K P χ (6 * d) (6 * r) ≠ 0 at hi
        have hr : r = d := by
          by_contra hn
          exact hi (by rw [probeIdealLocalCZero_one_class K P χ hχ, ite_eq_right hn])
        refine ⟨.inr (.inr (.inr (.inr (.inl d)))), ?_⟩
        simp only [probeLocalSurvivorIndex, hld, hr]
      | succ k =>
        cases k with
        | zero =>
          change probeIdealLocalCOne K P χ (6 * d) (6 * r) ≠ 0 at hi
          have hdr : d < r := by
            by_contra hn
            exact hi (by rw [probeIdealLocalCOne_one_class K P χ hχ hminus, ite_eq_right hn])
          refine ⟨.inr (.inr (.inr (.inr (.inr (d, r - (d + 1)))))), ?_⟩
          simp only [probeLocalSurvivorIndex, hld]
          have hr : d + 1 + (r - (d + 1)) = r := by omega
          rw [hr]
        | succ k => exact False.elim (hi (probeIdealLocalCoefficient_higher K P χ _ k _))
    · let d := l / 2
      have ht : 1 + 3 * l = 6 * d + 4 := by dsimp [d]; omega
      exact False.elim (hi (by rw [ht]; exact probeIdealLocalCoefficient_one_odd K P χ hχ hminus d k r))

theorem probeIdeal_supported_tsum (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (f : ProbeLocalRawIndex → ℂ)
    (hzero : ∀ i, probeIdealLocalCoefficient K P χ (probeLocalIndexDegree i)
      i.2.2.1 (6 * i.2.2.2) = 0 → f i = 0) :
    (∑' i : ProbeLocalRawIndex, f i) =
      ∑' j : ProbeLocalSurvivor, f (probeLocalSurvivorIndex j) := by
  symm
  apply probeLocalSurvivorIndex_injective.tsum_eq
  intro i hi
  apply probeIdealCoefficient_support K P χ hχ hminus i
  exact fun hc => hi (hzero i hc)

end

end ArtinMatthews.VaryingKummerAnalytic
