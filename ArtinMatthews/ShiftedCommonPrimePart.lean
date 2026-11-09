module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The literal common-prime part `(n,d^∞)` in the double Voronoi arithmetic. -/

namespace ArtinMatthews

/-- The full prime powers of `n` whose primes divide `d`. -/
def commonPrimePart (n d : ℕ) : ℕ :=
  (n.factorization.filter (fun p => p ∣ d)).prod (fun p k => p ^ k)

private theorem commonPrimePart_filter_le (n d : ℕ) :
    n.factorization.filter (fun p => p ∣ d) ≤ n.factorization := by
  intro p
  by_cases hp : p ∣ d <;> simp [hp]

theorem factorization_commonPrimePart (n d : ℕ) :
    (commonPrimePart n d).factorization = n.factorization.filter (fun p => p ∣ d) :=
  Nat.factorization_prod_pow_eq_self_of_le_factorization (commonPrimePart_filter_le n d)

theorem commonPrimePart_dvd (n d : ℕ) : commonPrimePart n d ∣ n :=
  Nat.prod_pow_dvd_of_le_factorization (commonPrimePart_filter_le n d)

theorem commonPrimePart_ne_zero {n : ℕ} (hn : n ≠ 0) (d : ℕ) :
    commonPrimePart n d ≠ 0 := by
  intro h
  exact hn (zero_dvd_iff.mp (h ▸ commonPrimePart_dvd n d))

theorem commonPrimePart_self {d : ℕ} (hd : d ≠ 0) : commonPrimePart d d = d := by
  have hf : d.factorization.filter (fun p => p ∣ d) = d.factorization := by
    ext p
    by_cases hp : p ∣ d
    · simp [hp]
    · simp [hp, Nat.factorization_eq_zero_of_not_dvd hp]
  unfold commonPrimePart
  rw [hf]
  exact Nat.prod_factorization_pow_eq_self hd

theorem commonPrimePart_mul {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (d : ℕ) :
    commonPrimePart (n * m) d = commonPrimePart n d * commonPrimePart m d := by
  apply Nat.eq_of_factorization_eq (commonPrimePart_ne_zero (mul_ne_zero hn hm) d)
    (mul_ne_zero (commonPrimePart_ne_zero hn d) (commonPrimePart_ne_zero hm d))
  rw [Nat.factorization_mul (commonPrimePart_ne_zero hn d) (commonPrimePart_ne_zero hm d)]
  rw [factorization_commonPrimePart, factorization_commonPrimePart,
    factorization_commonPrimePart, Nat.factorization_mul hn hm]
  intro p
  by_cases hp : p ∣ d <;> simp [hp]

/-- Removing the full common-prime part leaves an integer coprime to `d`. -/
theorem coprime_commonPrimePart_quotient {n : ℕ} (hn : n ≠ 0) (d : ℕ) :
    d.Coprime (n / commonPrimePart n d) := by
  apply Nat.coprime_of_dvd
  intro p hp hpd hpc
  have hq0 : n / commonPrimePart n d ≠ 0 :=
    Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
      (commonPrimePart_dvd n d)) (Nat.pos_of_ne_zero (commonPrimePart_ne_zero hn d)))
  have hf := (hp.dvd_iff_one_le_factorization hq0).mp hpc
  rw [Nat.factorization_div (commonPrimePart_dvd n d), Finsupp.tsub_apply,
    factorization_commonPrimePart] at hf
  simp [hpd] at hf

/-- Exact prime support of the literal common-prime part. -/
theorem prime_dvd_commonPrimePart_iff {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (d : ℕ) :
    p ∣ commonPrimePart n d ↔ p ∣ n ∧ p ∣ d := by
  rw [hp.dvd_iff_one_le_factorization (commonPrimePart_ne_zero hn d),
    factorization_commonPrimePart]
  by_cases hpd : p ∣ d
  · simp [hpd, hp.dvd_iff_one_le_factorization hn]
  · simp [hpd]

/-- All coprimality exclusions inherited from the supporting integer persist
for the full common-prime part. -/
theorem commonPrimePart_coprime {n d m : ℕ} (hn : n ≠ 0) (hcop : d.Coprime m) :
    (commonPrimePart n d).Coprime m := by
  apply Nat.coprime_of_dvd
  intro p hp hpD hpm
  have hdvd : p ∣ d.gcd m := Nat.dvd_gcd
    ((prime_dvd_commonPrimePart_iff hn hp d).mp hpD).2 hpm
  rw [hcop] at hdvd
  exact hp.ne_one (Nat.dvd_one.mp hdvd)

end ArtinMatthews
