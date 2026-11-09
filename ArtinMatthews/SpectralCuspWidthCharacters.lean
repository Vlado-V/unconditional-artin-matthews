module

public import ArtinMatthews.SpectralTrueWidthNormalizedMatrices
public import Mathlib.Algebra.Field.GeomSum


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite character cancellation for the width-index refinement,
including the common-period modes that do not descend to the true cusp. -/

noncomputable section
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

theorem atkinPhase_eq_one_iff_integer (x : ℝ) :
    atkinPhase x = 1 ↔ ∃ k : ℤ, x = (k : ℝ) := by
  constructor
  · intro hx
    obtain ⟨k,hk⟩ := Complex.exp_eq_one_iff.mp hx
    have he : (x : ℂ)*(2*(Real.pi : ℂ)*Complex.I) =
        (k : ℂ)*(2*(Real.pi : ℂ)*Complex.I) := by
      convert hk using 1
      ring
    have h := mul_right_cancel₀ Complex.two_pi_I_ne_zero he
    refine ⟨k,?_⟩
    exact_mod_cast h
  · rintro ⟨k,rfl⟩
    exact atkinPhase_int k

theorem atkinPhase_int_ratio_eq_one_iff (q : ℕ) (hq : 0 < q) (n : ℤ) :
    atkinPhase ((n : ℝ)/q) = 1 ↔ (q : ℤ) ∣ n := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [atkinPhase_eq_one_iff_integer]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    have he : (n : ℝ) = (q : ℝ)*k := by
      have h := (div_eq_iff hqR).mp hk
      nlinarith
    exact_mod_cast he
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    apply (div_eq_iff hqR).mpr
    have he : (n : ℝ) = (q : ℝ)*k := by exact_mod_cast hk
    nlinarith

theorem atkinPhase_mul_nat (x : ℝ) (k : ℕ) :
    atkinPhase (x*k) = (atkinPhase x)^k := by
  unfold atkinPhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem sum_fin_atkinPhase_int_ratio (q : ℕ) (hq : 0 < q) (n : ℤ) :
    (∑ a : Fin q, atkinPhase ((n : ℝ)*a.val/q)) =
      if (q : ℤ) ∣ n then (q : ℂ) else 0 := by
  classical
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have he (a : ℕ) : atkinPhase ((n : ℝ)*a/q) = (atkinPhase ((n : ℝ)/q))^a := by
    rw [← atkinPhase_mul_nat]
    congr 1
    ring
  simp_rw [he]
  by_cases hd : (q : ℤ) ∣ n
  · rw [ite_eq_left hd,(atkinPhase_int_ratio_eq_one_iff q hq n).mpr hd]
    simp only [one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  · rw [ite_eq_right hd,Fin.sum_univ_eq_sum_range]
    have hx : atkinPhase ((n : ℝ)/q) ≠ 1 := by
      exact fun h => hd ((atkinPhase_int_ratio_eq_one_iff q hq n).mp h)
    have hp : (atkinPhase ((n : ℝ)/q))^q = 1 := by
      rw [← atkinPhase_mul_nat]
      convert atkinPhase_int n using 1
      congr 1
      field_simp [hqR]
    rw [geom_sum_eq hx,hp,sub_self,zero_div]

theorem cuspWidth_character_sum (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (n : ℤ) :
    (∑ a : Fin (gamma0CuspFrequencyStep N r),
      atkinPhase ((n : ℝ)*(gamma0CuspTrueWidth N r : ℝ)*a.val/N)) =
      if (gamma0CuspFrequencyStep N r : ℤ) ∣ n then
        (gamma0CuspFrequencyStep N r : ℂ) else 0 := by
  have he : (gamma0CuspTrueWidth N r : ℝ)*gamma0CuspFrequencyStep N r = N := by
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N r
  have hq : 0 < gamma0CuspFrequencyStep N r := by
    have h := gamma0CuspFrequencyStep_mul_width N r
    have hN := NeZero.pos N
    nlinarith
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hqR : (gamma0CuspFrequencyStep N r : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  calc
    _ = ∑ a : Fin (gamma0CuspFrequencyStep N r),
        atkinPhase ((n : ℝ)*a.val/gamma0CuspFrequencyStep N r) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      field_simp [hN,hqR]
      linear_combination (n : ℝ)*(a.val : ℝ)*he
    _ = _ := sum_fin_atkinPhase_int_ratio _ hq n

end ArtinMatthews
