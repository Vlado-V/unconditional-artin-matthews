module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Numerical asymmetric-Schur and three-sector energy budgets. These
absorb fixed constants without an unproved operator estimate. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

theorem markedDirty_asymmetric_energy_budget {C G A₀ t : ℝ}
    (_hC : 0 ≤ C) (hG : 0 ≤ G) (hA : 0 ≤ A₀) (ht : max 1 (C+1) ≤ t) :
    t^(-(2*G+3*A₀+1))*(t^(-(2*G+3*A₀+1))+C*(t^A₀)^3) ≤ (t^(-G))^2 := by
  have ht₁ : 1 ≤ t := (le_max_left _ _).trans ht
  have htpos : 0 < t := zero_lt_one.trans_le ht₁
  have hct : C+1 ≤ t := (le_max_right _ _).trans ht
  have hsquare (a : ℝ) : t^(a*2)=(t^a)^2 := by
    simpa only [Nat.cast_ofNat] using Real.rpow_mul_natCast htpos.le a 2
  have hcube (a : ℝ) : t^(a*3)=(t^a)^3 := by
    simpa only [Nat.cast_ofNat] using Real.rpow_mul_natCast htpos.le a 3
  have he : -(2*G+3*A₀+1)*2 ≤ (-G)*2-1 := by linarith
  have hp : (t^(-(2*G+3*A₀+1)))^2 ≤ (t^(-G))^2/t := by
    calc
      _ = t^(-(2*G+3*A₀+1)*2) := (hsquare _).symm
      _ ≤ t^((-G)*2-1) := Real.rpow_le_rpow_of_exponent_le ht₁ he
      _ = t^((-G)*2)/t := by rw [Real.rpow_sub htpos,Real.rpow_one]
      _ = _ := by rw [hsquare]
  have hm : t^(-(2*G+3*A₀+1))*(t^A₀)^3 = (t^(-G))^2/t := by
    calc
      _ = t^(-(2*G+3*A₀+1)+A₀*3) := by rw [← hcube,← Real.rpow_add htpos]
      _ = t^((-G)*2-1) := by congr 1; ring
      _ = t^((-G)*2)/t := by rw [Real.rpow_sub htpos,Real.rpow_one]
      _ = _ := by rw [hsquare]
  calc
    _ = (t^(-(2*G+3*A₀+1)))^2+C*(t^(-(2*G+3*A₀+1))*(t^A₀)^3) := by ring
    _ ≤ (t^(-G))^2/t+C*((t^(-G))^2/t) := by rw [hm]; exact add_le_add hp le_rfl
    _ = (t^(-G))^2*((C+1)/t) := by ring
    _ ≤ (t^(-G))^2*1 := mul_le_mul_of_nonneg_left
      ((div_le_one htpos).mpr hct) (sq_nonneg _)
    _ = _ := mul_one _

theorem markedDirty_asymmetric_energy_eventually {C G A₀ : ℝ}
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hA : 0 ≤ A₀) :
    ∀ᶠ x : ℝ in atTop,
      (Real.log x)^(-(2*G+3*A₀+1))*
        ((Real.log x)^(-(2*G+3*A₀+1))+C*((Real.log x)^A₀)^3) ≤ ((Real.log x)^(-G))^2 := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (C+1)))] with x hx
  exact markedDirty_asymmetric_energy_budget hC hG hA hx

theorem markedDirty_norm_three_sq_le (a b c : ℂ) :
    ‖a+b+c‖^2 ≤ 3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have hn : ‖a+b+c‖ ≤ ‖a‖+‖b‖+‖c‖ := (norm_add_le (a+b) c).trans
    (add_le_add (norm_add_le a b) le_rfl)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

theorem markedDirty_weighted_three_energy_le {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ s,0 ≤ μ s) (f g h : Ω → ℂ) :
    (∑ s,μ s*‖f s+g s+h s‖^2) ≤
      3*((∑ s,μ s*‖f s‖^2)+(∑ s,μ s*‖g s‖^2)+(∑ s,μ s*‖h s‖^2)) := by
  calc
    _ ≤ ∑ s,μ s*(3*(‖f s‖^2+‖g s‖^2+‖h s‖^2)) :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left
        (markedDirty_norm_three_sq_le (f s) (g s) (h s)) (hμ s))
    _ = 3*∑ s,(μ s*‖f s‖^2+μ s*‖g s‖^2+μ s*‖h s‖^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib]

theorem markedDirty_three_log_budget {t G : ℝ} (ht : 3 ≤ t) :
    9*(t^(-(G+1)))^2 ≤ (t^(-G))^2 := by
  have htpos : 0 < t := by linarith
  have he : t^(-(G+1)) = t^(-G)/t := by
    rw [show -(G+1)= -G-1 by ring,Real.rpow_sub htpos,Real.rpow_one]
  rw [he]
  have hsmall : (3/t)^2 ≤ (1:ℝ) := pow_le_one₀ (by positivity) ((div_le_one htpos).mpr ht)
  calc
    _ = (t^(-G))^2*(3/t)^2 := by ring
    _ ≤ (t^(-G))^2*1 := mul_le_mul_of_nonneg_left hsmall (sq_nonneg _)
    _ = _ := mul_one _

end
end ArtinMatthews
