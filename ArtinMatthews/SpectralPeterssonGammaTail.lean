module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The literal incomplete Gamma mass of the height-truncated holomorphic
seed, with a lower ratio uniform in every weight at least two. -/
noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

def spectralPeterssonGammaTail (k : ℕ) (a : ℝ) : ℝ :=
  ∫ x in Ioi a, x^(k-2)*Real.exp (-x)

def spectralPeterssonGammaTailRatio (k : ℕ) (a : ℝ) : ℝ :=
  spectralPeterssonGammaTail k a / Real.Gamma ((k-1 : ℕ) : ℝ)

def spectralPeterssonTruncatedMass (k : ℕ) (n : ℕ+) (a : ℝ) : ℝ :=
  ∫ y in Ioi (a/(4*Real.pi*(n : ℝ))), y^(k-2)*Real.exp (-(4*Real.pi*(n : ℝ)*y))

private theorem petersson_gamma_integrable (p : ℕ) :
    IntegrableOn (fun x : ℝ => x^p*Real.exp (-x)) (Ioi (0 : ℝ)) := by
  have h := Real.GammaIntegral_convergent (show 0 < (p : ℝ)+1 by positivity)
  simpa only [add_sub_cancel_right,Real.rpow_natCast,mul_comm] using h

private theorem petersson_gamma_integral (p : ℕ) :
    (∫ x in Ioi (0 : ℝ), x^p*Real.exp (-x)) = Real.Gamma ((p : ℝ)+1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (show 0 < (p : ℝ)+1 by positivity) zero_lt_one
  simpa only [add_sub_cancel_right,Real.rpow_natCast,one_mul,one_div,inv_one,Real.one_rpow] using h

private theorem petersson_shift_indicator (g : ℝ → ℝ) (a : ℝ) :
    (fun x => (Ioi a).indicator g (x+a)) = (Ioi (0 : ℝ)).indicator (fun x => g (x+a)) := by
  funext x
  have h : a < x+a ↔ 0 < x := by constructor <;> intro hx <;> linarith
  simp only [Set.indicator_apply,mem_Ioi,h]

private theorem petersson_tail_shift (g : ℝ → ℝ) (a : ℝ) :
    (∫ x in Ioi a, g x) = ∫ x in Ioi (0 : ℝ), g (x+a) := by
  rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioi]
  rw [← petersson_shift_indicator]
  exact (integral_add_right_eq_self ((Ioi a).indicator g) a).symm

private theorem petersson_tail_shift_integrable (g : ℝ → ℝ) (a : ℝ)
    (hg : IntegrableOn g (Ioi a)) :
    IntegrableOn (fun x => g (x+a)) (Ioi (0 : ℝ)) := by
  have h := (hg.integrable_indicator measurableSet_Ioi).comp_add_right a
  rw [petersson_shift_indicator] at h
  exact (integrable_indicator_iff measurableSet_Ioi).mp h

theorem spectralPeterssonGammaTail_integrable (k : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun x : ℝ => x^(k-2)*Real.exp (-x)) (Ioi a) :=
  (petersson_gamma_integrable (k-2)).mono_set (Ioi_subset_Ioi ha)

theorem spectralPeterssonGammaTail_lower (k : ℕ) (hk : 2 ≤ k) (a : ℝ) (ha : 0 ≤ a) :
    Real.exp (-a)*Real.Gamma ((k-1 : ℕ) : ℝ) ≤ spectralPeterssonGammaTail k a := by
  have hk' : ((k-2 : ℕ) : ℝ)+1 = ((k-1 : ℕ) : ℝ) := by
    exact_mod_cast (show k-2+1 = k-1 by omega)
  rw [spectralPeterssonGammaTail,petersson_tail_shift]
  rw [← hk',← petersson_gamma_integral (k-2),← integral_const_mul]
  apply setIntegral_mono_on ((petersson_gamma_integrable (k-2)).const_mul _)
    (petersson_tail_shift_integrable _ a (spectralPeterssonGammaTail_integrable k a ha)) measurableSet_Ioi
  intro x hx
  change 0 < x at hx
  have hpow : x^(k-2) ≤ (x+a)^(k-2) := by gcongr; linarith
  rw [show -(x+a) = -a + -x by ring,Real.exp_add]
  calc
    _ = x^(k-2)*(Real.exp (-a)*Real.exp (-x)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (by positivity)

theorem spectralPeterssonGammaTail_upper (k : ℕ) (hk : 2 ≤ k) (a : ℝ) (ha : 0 ≤ a) :
    spectralPeterssonGammaTail k a ≤ Real.Gamma ((k-1 : ℕ) : ℝ) := by
  have hk' : ((k-2 : ℕ) : ℝ)+1 = ((k-1 : ℕ) : ℝ) := by
    exact_mod_cast (show k-2+1 = k-1 by omega)
  rw [spectralPeterssonGammaTail,← hk',← petersson_gamma_integral (k-2)]
  apply setIntegral_mono_set (petersson_gamma_integrable (k-2))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg hx.le _) (Real.exp_pos _).le
  · exact ae_of_all _ fun x hx => lt_of_le_of_lt ha hx

theorem spectralPeterssonGammaTailRatio_bounds (k : ℕ) (hk : 2 ≤ k) (a : ℝ) (ha : 0 ≤ a) :
    Real.exp (-a) ≤ spectralPeterssonGammaTailRatio k a ∧ spectralPeterssonGammaTailRatio k a ≤ 1 := by
  have hG : 0 < Real.Gamma ((k-1 : ℕ) : ℝ) := Real.Gamma_pos_of_pos (by exact_mod_cast (show 0 < k-1 by omega))
  constructor
  · exact (le_div_iff₀ hG).mpr (spectralPeterssonGammaTail_lower k hk a ha)
  · exact (div_le_one hG).mpr (spectralPeterssonGammaTail_upper k hk a ha)

end ArtinMatthews
