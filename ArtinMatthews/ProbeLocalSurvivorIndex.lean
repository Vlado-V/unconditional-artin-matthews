module

public import ArtinMatthews.ProbePrimeLocalCoefficient


set_option backward.privateInPublic true
@[expose] public section

/-! An explicit, injective enumeration of every possible nonzero local
index at j=0.  Coverage follows from the actual finite coefficient table. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical
noncomputable section

abbrev ProbeLocalRawIndex := Bool × ℕ × ℕ × ℕ
abbrev ProbeLocalSurvivor := ℕ ⊕ ℕ ⊕ (ℕ × ℕ) ⊕ ℕ ⊕ ℕ ⊕ (ℕ × ℕ)

def probeLocalSurvivorIndex : ProbeLocalSurvivor → ProbeLocalRawIndex
  | .inl r => (false, 0, 0, r)
  | .inr (.inl k) => (false, 0, k + 1, 0)
  | .inr (.inr (.inl (d, s))) => (false, 2 * (d + 1), 0, d + 1 + s)
  | .inr (.inr (.inr (.inl d))) => (false, 2 * (d + 1), 1, d + 1)
  | .inr (.inr (.inr (.inr (.inl d)))) => (true, 2 * d, 0, d)
  | .inr (.inr (.inr (.inr (.inr (d, s))))) => (true, 2 * d, 1, d + 1 + s)

def probeLocalSurvivorRetract (i : ProbeLocalRawIndex) : ProbeLocalSurvivor :=
  if i.1 then
    if i.2.2.1 = 0 then .inr (.inr (.inr (.inr (.inl (i.2.1 / 2)))))
    else .inr (.inr (.inr (.inr (.inr (i.2.1 / 2, i.2.2.2 - (i.2.1 / 2 + 1))))))
  else if i.2.1 = 0 then
    if i.2.2.1 = 0 then .inl i.2.2.2 else .inr (.inl (i.2.2.1 - 1))
  else if i.2.2.1 = 0 then
    .inr (.inr (.inl (i.2.1 / 2 - 1, i.2.2.2 - i.2.1 / 2)))
  else .inr (.inr (.inr (.inl (i.2.1 / 2 - 1))))

theorem probeLocalSurvivorRetract_leftInverse :
    Function.LeftInverse probeLocalSurvivorRetract probeLocalSurvivorIndex := by
  rintro (r | k | ⟨d, s⟩ | d | d | ⟨d, s⟩) <;>
    simp [probeLocalSurvivorRetract, probeLocalSurvivorIndex, Nat.mul_comm,
      Nat.add_comm, Nat.add_left_comm] <;> omega

theorem probeLocalSurvivorIndex_injective : Function.Injective probeLocalSurvivorIndex :=
  probeLocalSurvivorRetract_leftInverse.injective

def probeLocalIndexDegree (i : ProbeLocalRawIndex) : ℕ :=
  (if i.1 then 1 else 0) + 3 * i.2.1

variable (K : Type*) [Field K] [NumberField K]

theorem probeLocalCoefficient_support (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (i : ProbeLocalRawIndex)
    (hi : probePrimeLocalCoefficient K p hp.ne_zero χ (probeLocalIndexDegree i)
      i.2.2.1 (6 * i.2.2.2) ≠ 0) : i ∈ Set.range probeLocalSurvivorIndex := by
  rcases i with ⟨e, l, k, r⟩
  cases e with
  | false =>
    simp only [probeLocalIndexDegree, Bool.false_eq_true, ite_false, zero_add] at hi
    change probePrimeLocalCoefficient K p hp.ne_zero χ (3 * l) k (6 * r) ≠ 0 at hi
    by_cases hl : l = 0
    · subst l
      cases k with
      | zero => exact ⟨.inl r, rfl⟩
      | succ k =>
        have hr : r = 0 := by
          by_contra hn
          apply hi
          simp only [mul_zero, probePrimeLocalCoefficient_zero_succ K p hp,
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
          change probePrimeLocalCZero K p hp.ne_zero χ (6 * d + 5) (6 * r) ≠ 0 at hi
          have hdr : d < r := by
            by_contra hn
            exact hi (by rw [probePrimeLocalCZero_zero_class K p hp χ hχ, ite_eq_right hn])
          refine ⟨.inr (.inr (.inl (d, r - (d + 1)))), ?_⟩
          simp only [probeLocalSurvivorIndex, hld]
          have hr : d + 1 + (r - (d + 1)) = r := by omega
          rw [hr]
        | succ k =>
          cases k with
          | zero =>
            change probePrimeLocalCOne K p hp.ne_zero χ (6 * d + 5) (6 * r) ≠ 0 at hi
            have hr : r = d + 1 := by
              by_contra hn
              exact hi (by rw [probePrimeLocalCOne_zero_class K p hp χ hχ hminus, ite_eq_right hn])
            refine ⟨.inr (.inr (.inr (.inl d))), ?_⟩
            simp only [probeLocalSurvivorIndex, hld, hr]
          | succ k => exact False.elim (hi (probePrimeLocalCoefficient_higher K p hp χ _ k _))
      · let d := l / 2
        have ht : 3 * l = 6 * d + 3 := by dsimp [d]; omega
        exact False.elim (hi (by rw [ht]; exact probePrimeLocalCoefficient_zero_odd K p hp χ hχ hminus d k r))
  | true =>
    change probePrimeLocalCoefficient K p hp.ne_zero χ (1 + 3 * l) k (6 * r) ≠ 0 at hi
    by_cases heven : l % 2 = 0
    · let d := l / 2
      have hld : l = 2 * d := by dsimp [d]; omega
      have ht : 1 + 3 * l = 6 * d + 1 := by omega
      rw [ht] at hi
      cases k with
      | zero =>
        change probePrimeLocalCZero K p hp.ne_zero χ (6 * d) (6 * r) ≠ 0 at hi
        have hr : r = d := by
          by_contra hn
          exact hi (by rw [probePrimeLocalCZero_one_class K p hp χ hχ, ite_eq_right hn])
        refine ⟨.inr (.inr (.inr (.inr (.inl d)))), ?_⟩
        simp only [probeLocalSurvivorIndex, hld, hr]
      | succ k =>
        cases k with
        | zero =>
          change probePrimeLocalCOne K p hp.ne_zero χ (6 * d) (6 * r) ≠ 0 at hi
          have hdr : d < r := by
            by_contra hn
            exact hi (by rw [probePrimeLocalCOne_one_class K p hp χ hχ hminus, ite_eq_right hn])
          refine ⟨.inr (.inr (.inr (.inr (.inr (d, r - (d + 1)))))), ?_⟩
          simp only [probeLocalSurvivorIndex, hld]
          have hr : d + 1 + (r - (d + 1)) = r := by omega
          rw [hr]
        | succ k => exact False.elim (hi (probePrimeLocalCoefficient_higher K p hp χ _ k _))
    · let d := l / 2
      have ht : 1 + 3 * l = 6 * d + 4 := by dsimp [d]; omega
      exact False.elim (hi (by rw [ht]; exact probePrimeLocalCoefficient_one_odd K p hp χ hχ hminus d k r))

theorem probeLocal_supported_tsum (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (f : ProbeLocalRawIndex → ℂ)
    (hzero : ∀ i, probePrimeLocalCoefficient K p hp.ne_zero χ (probeLocalIndexDegree i)
      i.2.2.1 (6 * i.2.2.2) = 0 → f i = 0) :
    (∑' i : ProbeLocalRawIndex, f i) =
      ∑' j : ProbeLocalSurvivor, f (probeLocalSurvivorIndex j) := by
  symm
  apply probeLocalSurvivorIndex_injective.tsum_eq
  intro i hi
  apply probeLocalCoefficient_support K p hp χ hχ hminus i
  exact fun hc => hi (hzero i hc)

end

end ArtinMatthews.VaryingKummerAnalytic
