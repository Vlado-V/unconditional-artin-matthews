module

public import ArtinMatthews.MarkedRootGridBudget


set_option backward.privateInPublic true
@[expose] public section

/-! A logarithmic bound per actual edge costs the corresponding multiple
of the moment exponent, with the entire path length retained. -/

noncomputable section
namespace ArtinMatthews
open Filter

theorem markedPhysicalCoordinate_log_power (C A : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop,∀ (Q : ℝ) (n : ℕ),1 ≤ Q → Q ≤ (Real.log x)^A →
      (C*Q^3)^n ≤ (Real.log x)^((3*A+1)*(n:ℝ)) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max C 1))] with x hx
  intro Q n hQ hQhi
  have hL : 1 ≤ Real.log x := (le_max_right _ _).trans hx
  have hLp : 0 < Real.log x := zero_lt_one.trans_le hL
  have hC' : C ≤ Real.log x := (le_max_left _ _).trans hx
  have hb : C*Q^3 ≤ (Real.log x)^(3*A+1) := by
    calc
      _ ≤ Real.log x*((Real.log x)^A)^3 := mul_le_mul hC'
        (pow_le_pow_left₀ (zero_le_one.trans hQ) hQhi 3) (by positivity) hLp.le
      _ = (Real.log x)^(1:ℝ)*(Real.log x)^(A*(3:ℝ)) := by
        rw [Real.rpow_one]
        congr 1
        simpa only [Nat.cast_ofNat] using (Real.rpow_mul_natCast hLp.le A 3).symm
      _ = _ := by rw [← Real.rpow_add hLp]; congr 1; ring
  exact (pow_le_pow_left₀ (by positivity) hb n).trans_eq
    (Real.rpow_mul_natCast hLp.le (3*A+1) n).symm

theorem markedPhysicalCoordinate_log_absorption (C A G : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop,∀ (Q E : ℝ) (n : ℕ),1 ≤ Q → Q ≤ (Real.log x)^A → 0 ≤ E →
      E ≤ (Real.log x)^(-(G+3*A+1)*(n:ℝ)) →
      (C*Q^3)^n*E ≤ (Real.log x)^(-G*(n:ℝ)) := by
  filter_upwards [markedPhysicalCoordinate_log_power C A hC,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hL
  intro Q E n hQ hQhi hE hEhi
  calc
    _ ≤ (Real.log x)^((3*A+1)*(n:ℝ))*(Real.log x)^(-(G+3*A+1)*(n:ℝ)) :=
      mul_le_mul (hx Q n hQ hQhi) hEhi hE (Real.rpow_nonneg (zero_le_one.trans hL) _)
    _ = _ := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hL)]
      congr 1
      ring

end ArtinMatthews
