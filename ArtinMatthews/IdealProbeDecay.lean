module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

/-! The probe number is chosen before the full label dimension. Its
fixed survivor factor gives arbitrary logarithmic decay across blocks. -/
namespace ArtinMatthews

theorem idealProbe_choose (η : ℝ) (hη : 0 < η) :
    ∃ m : ℕ,1 ≤ m ∧ 0 < (2/(m+1 : ℕ) : ℝ) ∧ (2/(m+1 : ℕ) : ℝ) < min 1 η := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max 2 (2/η))
  have hm2 : (2:ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hdiv : 2/η < (m:ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
  have hmpos : 0 < ((m+1:ℕ):ℝ) := by positivity
  have hval : (2/((m+1:ℕ):ℝ)) < η := by
    apply (div_lt_iff₀ hmpos).mpr
    have h := (div_lt_iff₀ hη).mp hdiv
    push_cast
    nlinarith
  refine ⟨m,?_,by positivity,lt_min ?_ hval⟩
  · have : (1:ℝ) ≤ m := by linarith
    exact_mod_cast this
  · rw [div_lt_one hmpos]
    push_cast
    linarith

theorem idealProbe_logarithmic_block_choice (c E : ℝ) (hc : 0 < c) (hE : 0 ≤ E) :
    ∃ m : ℕ,1 ≤ m ∧ 0 < (2/(m+1 : ℕ) : ℝ) ∧ (2/(m+1 : ℕ) : ℝ) < 1 ∧
      ∀ (L : ℝ) (s : ℕ),1 ≤ L → c*Real.log L/3 ≤ s →
        (2/(m+1 : ℕ) : ℝ)^s ≤ L^(-2*E : ℝ) := by
  obtain ⟨m,hm,hθ,hsmall⟩ := idealProbe_choose (Real.exp (-6*(E+3)/c)) (Real.exp_pos _)
  have hθ1 : (2/(m+1 : ℕ) : ℝ) < 1 := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hlog : Real.log (2/(m+1 : ℕ) : ℝ) ≤ -6*(E+3)/c := by
    have h := Real.log_lt_log hθ (lt_of_lt_of_le hsmall (min_le_right _ _))
    simpa only [Real.log_exp] using h.le
  refine ⟨m,hm,hθ,hθ1,?_⟩
  intro L s hL hs
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hn : -6*(E+3)/c ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by nlinarith) hc.le
  have h1 := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg s : (0:ℝ) ≤ s)
  have h2 := mul_le_mul_of_nonpos_right hs hn
  have hcalc : (c*Real.log L/3)*(-6*(E+3)/c) = -2*(E+3)*Real.log L := by
    field_simp [hc.ne']
    ring
  rw [hcalc] at h2
  have hexp : Real.log (2/(m+1 : ℕ) : ℝ)*(s:ℝ) ≤ Real.log L*(-2*E) := by
    nlinarith
  rw [← Real.rpow_natCast,Real.rpow_def_of_pos hθ,Real.rpow_def_of_pos hLpos]
  exact Real.exp_le_exp.mpr hexp

end ArtinMatthews
