module

public import ArtinMatthews.SpectralCuspTranslationAdmissibility


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine least positive integral cusp period, with its complete
translation criterion and exact frequency step inside the common period N. -/

noncomputable section
open Matrix
open scoped MatrixGroups

namespace ArtinMatthews

theorem cuspWidth_positive_period_exists (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    ∃ w : ℕ, 0 < w ∧ (N : ℤ) ∣ (w : ℤ) * (r 1 0)^2 :=
  ⟨N,NeZero.pos N,dvd_mul_right _ _⟩

def gamma0CuspTrueWidth (N : ℕ) [NeZero N] (r : SL(2, ℤ)) : ℕ :=
  Nat.find (cuspWidth_positive_period_exists N r)

theorem gamma0CuspTrueWidth_pos (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    0 < gamma0CuspTrueWidth N r := (Nat.find_spec (cuspWidth_positive_period_exists N r)).1

theorem gamma0CuspTrueWidth_period (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    (N : ℤ) ∣ (gamma0CuspTrueWidth N r : ℤ) * (r 1 0)^2 :=
  (Nat.find_spec (cuspWidth_positive_period_exists N r)).2

theorem gamma0CuspTrueWidth_minimal (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (w : ℕ) (hw : 0 < w) (hperiod : (N : ℤ) ∣ (w : ℤ) * (r 1 0)^2) :
    gamma0CuspTrueWidth N r ≤ w := Nat.find_min' _ ⟨hw,hperiod⟩

theorem minimal_positive_mul_divisor (N a : ℤ) (w : ℕ) (hw : 0 < w)
    (hperiod : N ∣ (w : ℤ)*a)
    (hmin : ∀ j : ℕ, 0 < j → N ∣ (j : ℤ)*a → w ≤ j) (k : ℤ) :
    N ∣ k*a ↔ (w : ℤ) ∣ k := by
  have hwZ : 0 < (w : ℤ) := by exact_mod_cast hw
  constructor
  · intro hk
    have hrem : N ∣ (k % w)*a := by
      have he : (k % w)*a = k*a - ((w : ℤ)*a)*(k / w) := by
        have h := Int.emod_add_mul_ediv k w
        linear_combination a*h
      rw [he]
      exact dvd_sub hk (dvd_mul_of_dvd_left hperiod _)
    have hnonneg : 0 ≤ k % w := Int.emod_nonneg _ hwZ.ne'
    have hlt : k % w < w := Int.emod_lt_of_pos _ hwZ
    have hzero : k % w = 0 := by
      by_contra hn
      have hp : 0 < k % w := lt_of_le_of_ne hnonneg (Ne.symm hn)
      have ht : ((k % w).toNat : ℤ) = k % w := Int.toNat_of_nonneg hnonneg
      have htp : 0 < (k % w).toNat := by exact_mod_cast (show (0 : ℤ) < ((k % w).toNat : ℤ) by simpa only [ht] using hp)
      have hnp : N ∣ ((k % w).toNat : ℤ)*a := by simpa only [ht] using hrem
      have hm := hmin _ htp hnp
      have hmZ : (w : ℤ) ≤ ((k % w).toNat : ℤ) := by exact_mod_cast hm
      rw [ht] at hmZ
      omega
    exact Int.dvd_of_emod_eq_zero hzero
  · rintro ⟨q,rfl⟩
    have h := dvd_mul_of_dvd_left hperiod q
    convert h using 1
    ring

theorem gamma0CuspTrueWidth_translation_iff (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (k : ℤ) :
    r⁻¹ * integerTranslation k * r ∈ CongruenceSubgroup.Gamma0 N ↔
      (gamma0CuspTrueWidth N r : ℤ) ∣ k := by
  rw [cusp_conjugate_translation_mem_iff]
  exact minimal_positive_mul_divisor (N : ℤ) ((r 1 0)^2) (gamma0CuspTrueWidth N r)
    (gamma0CuspTrueWidth_pos N r) (gamma0CuspTrueWidth_period N r)
    (gamma0CuspTrueWidth_minimal N r) k

theorem gamma0CuspTrueWidth_dvd_level (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    gamma0CuspTrueWidth N r ∣ N := by
  have hp := gamma0_conjugate_period_translation_mem N r 1
  rw [mul_one] at hp
  have h := (gamma0CuspTrueWidth_translation_iff N r (N : ℤ)).mp hp
  exact_mod_cast h

def gamma0CuspFrequencyStep (N : ℕ) [NeZero N] (r : SL(2, ℤ)) : ℕ :=
  N / gamma0CuspTrueWidth N r

theorem gamma0CuspFrequencyStep_mul_width (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    gamma0CuspTrueWidth N r * gamma0CuspFrequencyStep N r = N :=
  Nat.mul_div_cancel' (gamma0CuspTrueWidth_dvd_level N r)

theorem gamma0CuspFrequencyStep_admissible_iff (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) :
    (N : ℤ) ∣ n * (gamma0CuspTrueWidth N r : ℤ) ↔
      (gamma0CuspFrequencyStep N r : ℤ) ∣ n := by
  have he : (gamma0CuspTrueWidth N r : ℤ) * (gamma0CuspFrequencyStep N r : ℤ) = N := by
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N r
  have hw : (gamma0CuspTrueWidth N r : ℤ) ≠ 0 := by
    exact_mod_cast (gamma0CuspTrueWidth_pos N r).ne'
  constructor
  · rintro ⟨q,hq⟩
    refine ⟨q,?_⟩
    apply mul_left_cancel₀ hw
    calc
      (gamma0CuspTrueWidth N r : ℤ) * n = n * (gamma0CuspTrueWidth N r : ℤ) := mul_comm _ _
      _ = (N : ℤ) * q := hq
      _ = (gamma0CuspTrueWidth N r : ℤ) * ((gamma0CuspFrequencyStep N r : ℤ) * q) := by rw [← he]; ring
  · rintro ⟨q,rfl⟩
    refine ⟨q,?_⟩
    rw [← he]
    ring

end ArtinMatthews
