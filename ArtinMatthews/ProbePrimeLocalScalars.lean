module

public import ArtinMatthews.ProbeCoherentPrimeGauss


set_option backward.privateInPublic true
@[expose] public section

/-! Literal local sums with outer modulus one or one prime.  Here the index
`n` means that the positive inner modulus is `p^(n+1)`. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField OAI.SevenEighths
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probePrimeResidueTransform (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (v : ℕ) (h : 𝓞 K) : ℂ :=
  ∑' x : ((𝓞 K) ⧸ Ideal.span {p}), (χ ^ v) x *
    probePrimePhase K p hp (Ideal.Quotient.mk _ h * x)

def probePrimeTau (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) : ℂ :=
  ∑' x : ((𝓞 K) ⧸ Ideal.span {p}), χ x * probePrimePhase K p hp x

def probePrimeScalarOne (p : 𝓞 K) (hp : p ≠ 0)
    (χ ξ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : 𝓞 K) : ℂ :=
  ∑' d : ((𝓞 K) ⧸ Ideal.span {p}), χ d *
    probePrimePowerGauss K p hp ξ n (h - p ^ n * Quotient.out d)

theorem probePrimeScalarOne_eq (p : 𝓞 K) (hp : Prime p)
    (χ ξ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : 𝓞 K) :
    probePrimeScalarOne K p hp.ne_zero χ ξ n h =
      χ⁻¹ (-1) * probePrimeTau K p hp.ne_zero χ *
        probePrimePowerGauss K p hp.ne_zero (ξ * χ⁻¹) n h := by
  let : (Ideal.span {p} : Ideal (𝓞 K)).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Field ((𝓞 K) ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ Ideal.span {p}) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  let : Fintype ((𝓞 K) ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hτ : probePrimeTau K p hp.ne_zero χ =
      gaussSum χ (probePrimePhase K p hp.ne_zero) := by
    rw [probePrimeTau, tsum_fintype]
    rfl
  rw [hτ]
  by_cases hd : p ^ n ∣ h
  · obtain ⟨k, rfl⟩ := hd
    have hmk (d : ((𝓞 K) ⧸ Ideal.span {p})) :
        Ideal.Quotient.mk (Ideal.span {p}) (k - Quotient.out d) =
          Ideal.Quotient.mk _ k - d := by
      rw [map_sub, Ideal.Quotient.mk_out]
    have hs : probePrimeScalarOne K p hp.ne_zero χ ξ n (p ^ n * k) =
        (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
          ∑ d : ((𝓞 K) ⧸ Ideal.span {p}), χ d *
            ProbeGauss.frequencyGauss ξ (probePrimePhase K p hp.ne_zero)
              (Ideal.Quotient.mk _ k - d) := by
      unfold probePrimeScalarOne
      rw [tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [← mul_sub, probePrimePowerGauss_lift, tsum_fintype]
      simp only [hmk, ProbeGauss.frequencyGauss]
      ring
    rw [hs, ProbeGauss.finite_gauss_convolution, probePrimePowerGauss_lift,
      tsum_fintype]
    unfold ProbeGauss.frequencyGauss
    ring
  · rw [probePrimePowerGauss_zero_off_support K p hp.ne_zero (ξ * χ⁻¹) n h hd,
      mul_zero]
    unfold probePrimeScalarOne
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro d _
    have hnd : ¬ p ^ n ∣ h - p ^ n * Quotient.out d := by
      intro hh
      apply hd
      have he := dvd_add hh (dvd_mul_right (p ^ n) (Quotient.out d))
      simpa only [sub_add_cancel] using he
    rw [probePrimePowerGauss_zero_off_support K p hp.ne_zero ξ n _ hnd, mul_zero]

def probeLocalExactQuotient (a b : 𝓞 K) (h : b ∣ a) : 𝓞 K := h.choose

omit [NumberField K] in
theorem probeLocalExactQuotient_spec (a b : 𝓞 K) (h : b ∣ a) :
    a = b * probeLocalExactQuotient K a b h := h.choose_spec

omit [NumberField K] in
theorem probeLocalExactQuotient_mul (b a : 𝓞 K) (hb : b ≠ 0) (h : b ∣ b * a) :
    probeLocalExactQuotient K (b * a) b h = a := by
  apply mul_left_cancel₀ hb
  exact (probeLocalExactQuotient_spec K (b * a) b h).symm

def probePrimeLocalCZero (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n J : ℕ) : ℂ :=
  probePrimePowerGauss K p hp (χ ^ (n + 1)) n (p ^ J)

def probePrimeLocalCOne (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n J : ℕ) : ℂ :=
  ∑' d : ((𝓞 K) ⧸ Ideal.span {p}),
    if hd : p ∣ p ^ J - p ^ (n + 1) * Quotient.out d then
      χ d * probePrimePowerGauss K p hp (χ ^ (n + 1)) n
        (probeLocalExactQuotient K _ p hd)
    else 0

theorem probePrimeLocalCZero_eq (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n J : ℕ) :
    probePrimeLocalCZero K p hp.ne_zero χ n J =
      if n ≤ J then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
        probePrimeResidueTransform K p hp.ne_zero χ (n + 1) (p ^ (J - n)) else 0 := by
  unfold probePrimeLocalCZero
  by_cases hnJ : n ≤ J
  · rw [ite_eq_left hnJ]
    have hpow : p ^ J = p ^ n * p ^ (J - n) := by
      rw [← pow_add, Nat.add_sub_of_le hnJ]
    rw [hpow, probePrimePowerGauss_lift]
    rfl
  · rw [ite_eq_right hnJ]
    exact probePrimePowerGauss_zero_off_support K p hp.ne_zero _ n _
      (fun hd => hnJ ((pow_dvd_pow_iff hp.ne_zero hp.not_isUnit).mp hd))

theorem probePrimeLocalCOne_zero (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n : ℕ) :
    probePrimeLocalCOne K p hp.ne_zero χ n 0 = 0 := by
  unfold probePrimeLocalCOne
  have hd (d : ((𝓞 K) ⧸ Ideal.span {p})) :
      ¬ p ∣ p ^ 0 - p ^ (n + 1) * Quotient.out d := by
    intro hh
    apply hp.not_dvd_one
    have he := dvd_add hh ((dvd_pow_self p (Nat.succ_ne_zero n)).mul_right (Quotient.out d))
    simpa only [pow_zero, sub_add_cancel] using he
  calc
    _ = ∑' _d : ((𝓞 K) ⧸ Ideal.span {p}), (0 : ℂ) :=
      tsum_congr (fun d => dite_eq_right (hd d))
    _ = 0 := tsum_zero

theorem probePrimeLocalCOne_succ (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n J : ℕ) :
    probePrimeLocalCOne K p hp χ n (J + 1) =
      probePrimeScalarOne K p hp χ (χ ^ (n + 1)) n (p ^ J) := by
  unfold probePrimeLocalCOne probePrimeScalarOne
  apply tsum_congr
  intro d
  have he : p ^ (J + 1) - p ^ (n + 1) * Quotient.out d =
      p * (p ^ J - p ^ n * Quotient.out d) := by
    simp only [pow_succ']
    ring
  simp only [he, dvd_mul_right, dite_eq_left]
  rw [probeLocalExactQuotient_mul K p _ hp]

theorem probePrimeLocalCOne_eq (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : χ (-1) = 1) (n J : ℕ) :
    probePrimeLocalCOne K p hp.ne_zero χ n J =
      if n + 1 ≤ J then probePrimeTau K p hp.ne_zero χ *
        (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
        probePrimeResidueTransform K p hp.ne_zero χ n (p ^ (J - (n + 1))) else 0 := by
  cases J with
  | zero => rw [probePrimeLocalCOne_zero K p hp]; simp
  | succ J =>
    rw [probePrimeLocalCOne_succ, probePrimeScalarOne_eq K p hp, MulChar.inv_apply_eq_inv',
      hχ, inv_one, one_mul, pow_succ, mul_inv_cancel_right]
    by_cases hnJ : n ≤ J
    · rw [ite_eq_left (Nat.succ_le_succ hnJ)]
      have hpow : p ^ J = p ^ n * p ^ (J - n) := by
        rw [← pow_add, Nat.add_sub_of_le hnJ]
      rw [hpow, probePrimePowerGauss_lift]
      simp only [Nat.succ_sub_succ_eq_sub, probePrimeResidueTransform]
      ring
    · rw [ite_eq_right (fun h => hnJ (Nat.succ_le_succ_iff.mp h)),
        probePrimePowerGauss_zero_off_support K p hp.ne_zero _ n _
          (fun hd => hnJ ((pow_dvd_pow_iff hp.ne_zero hp.not_isUnit).mp hd)), mul_zero]

end

end ArtinMatthews.VaryingKummerAnalytic
