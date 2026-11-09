module

public import ArtinMatthews.MarkedMajorArcDivisorReindex
public import ArtinMatthews.GiantWindowArithmetic
public import ArtinMatthews.MarkedMajorArcProductPolynomial


set_option backward.privateInPublic true
@[expose] public section

/-! Exact factorization of the centered marked endpoint after removing its
distinguished small mark. The subtraction retains the original reciprocal
giant-prime constant. -/

namespace ArtinMatthews

open Finset

noncomputable section

/-- The constant branch reindexes by the actual small-prime divisor. -/
theorem sourceComparison_removed_constant_eq (S : Finset ℕ) (N : ℕ)
    (a F : ℕ → ℂ) (hS : ∀ p ∈ S, 0 < p) (hF : ∀ n, N < n → F n = 0) :
    (∑ w ∈ Ioc 0 N, (∑ p ∈ activeDivisors S w, a (w/p))*F w) =
      ∑ p ∈ S, ∑ n ∈ Ioc 0 N, a n*F (p*n) := by
  classical
  simp only [activeDivisors, sum_mul, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  simp_rw [ite_mul, zero_mul]
  rw [marked_sum_Ioc_dvd_reindex (hS p hp), Nat.zero_div]
  have hsub : Ioc 0 (N/p) ⊆ Ioc 0 N := fun n hn =>
    mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2.trans (Nat.div_le_self _ _)⟩
  calc
    _ = ∑ n ∈ Ioc 0 (N/p), a n*F (p*n) := by
      apply sum_congr rfl
      intro n _
      rw [Nat.mul_div_cancel_left _ (hS p hp)]
    _ = _ := sum_subset hsub fun n hn hnp => by
      have hn' : N/p < n := by
        apply lt_of_not_ge
        exact fun h => hnp (mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,h⟩)
      rw [hF _ (by simpa only [mul_comm] using (Nat.div_lt_iff_lt_mul (hS p hp)).mp hn'), mul_zero]

/-- The positive branch reindexes by the actual small and giant primes.
Their coprimality identifies the original pair of divisibility conditions. -/
theorem sourceComparison_removed_tuple_eq (S G : Finset ℕ) (N : ℕ)
    (a F : ℕ → ℂ) (hS : ∀ p ∈ S, p.Prime) (hG : ∀ ell ∈ G, ell.Prime)
    (hdis : Disjoint S G) (hinv : ∀ ell ∈ G, ∀ n, a (ell*n)=a n)
    (hF : ∀ n, N < n → F n = 0) :
    (∑ w ∈ Ioc 0 N, (giantWindowDivisorCount G w : ℂ)*
      (∑ p ∈ activeDivisors S w, a (w/p))*F w) =
      ∑ p ∈ S, ∑ ell ∈ G, ∑ n ∈ Ioc 0 N, a n*F (p*ell*n) := by
  classical
  have he (w : ℕ) : (giantWindowDivisorCount G w : ℂ) =
      ∑ ell ∈ G, if ell ∣ w then (1:ℂ) else 0 := by
    unfold giantWindowDivisorCount
    push_cast
    apply sum_congr rfl
    intro ell _
    split_ifs <;> norm_num
  have hinner (w : ℕ) :
      (giantWindowDivisorCount G w : ℂ)*(∑ p ∈ activeDivisors S w, a (w/p))*F w =
      ∑ p ∈ S, ∑ ell ∈ G, if p*ell ∣ w then a (w/p)*F w else 0 := by
    rw [he, mul_comm (∑ ell ∈ G, _), sum_mul, sum_mul]
    unfold activeDivisors
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    have hs (ell : ℕ) (hell : ell ∈ G) : p*ell ∣ w ↔ p ∣ w ∧ ell ∣ w := by
      have hne : p ≠ ell := fun heq => (disjoint_left.mp hdis hp) (heq ▸ hell)
      have hcop := (Nat.coprime_primes (hS p hp) (hG ell hell)).mpr hne
      exact ⟨fun h => ⟨(dvd_mul_right _ _).trans h, (dvd_mul_left _ _).trans h⟩,
        fun h => hcop.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
    by_cases hpw : p ∣ w
    · rw [ite_eq_left hpw, mul_sum, sum_mul]
      apply sum_congr rfl
      intro ell hell
      by_cases hellw : ell ∣ w
      · simp [hellw, (hs ell hell).mpr ⟨hpw,hellw⟩]
      · have hn : ¬ p*ell ∣ w := fun h => hellw ((hs ell hell).mp h).2
        simp [hellw, hn]
    · rw [ite_eq_right hpw]
      symm
      apply sum_eq_zero
      intro ell hell
      exact ite_eq_right (fun h => hpw ((hs ell hell).mp h).1)
  simp_rw [hinner]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [sum_comm]
  apply sum_congr rfl
  intro ell hell
  have hd := Nat.mul_pos (hS p hp).pos (hG ell hell).pos
  rw [marked_sum_Ioc_dvd_reindex hd, Nat.zero_div]
  have hsub : Ioc 0 (N/(p*ell)) ⊆ Ioc 0 N := fun n hn =>
    mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2.trans (Nat.div_le_self _ _)⟩
  calc
    _ = ∑ n ∈ Ioc 0 (N/(p*ell)), a n*F (p*ell*n) := by
      apply sum_congr rfl
      intro n _
      rw [mul_assoc p ell n, Nat.mul_div_cancel_left _ (hS p hp).pos, hinv ell hell n]
    _ = _ := sum_subset hsub fun n hn hnp => by
      have hn' : N/(p*ell) < n := by
        apply lt_of_not_ge
        exact fun h => hnp (mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,h⟩)
      rw [hF _ (by simpa only [mul_comm (p*ell)] using (Nat.div_lt_iff_lt_mul hd).mp hn'), mul_zero]

theorem sourceComparison_removed_centered_eq (S G : Finset ℕ) (N : ℕ) (V C : ℝ)
    (a F : ℕ → ℂ) (hS : ∀ p ∈ S, p.Prime) (hG : ∀ ell ∈ G, ell.Prime)
    (hdis : Disjoint S G) (hinv : ∀ ell ∈ G, ∀ n, a (ell*n)=a n)
    (hF : ∀ n, N < n → F n = 0) :
    (∑ w ∈ Ioc 0 N, (bandReciprocalMass S : ℂ)⁻¹ *
      (∑ p ∈ activeDivisors S w, a (w/p)) *
        ((giantWindowDivisorCount G w : ℂ) - (C:ℂ))*F w) / V =
      ((bandReciprocalMass S : ℂ)⁻¹ / V) *
        ((∑ p ∈ S, ∑ ell ∈ G, ∑ n ∈ Ioc 0 N, a n*F (p*ell*n)) -
          (C:ℂ)*(∑ p ∈ S, ∑ n ∈ Ioc 0 N, a n*F (p*n))) := by
  rw [← sourceComparison_removed_constant_eq S N a F (fun p hp => (hS p hp).pos) hF,
    ← sourceComparison_removed_tuple_eq S G N a F hS hG hdis hinv hF]
  rw [mul_sub, ← mul_assoc _ (C:ℂ), mul_sum, mul_sum, ← sum_sub_distrib, sum_div]
  apply sum_congr rfl
  intro w _
  ring

end
end ArtinMatthews
