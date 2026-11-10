module

public import ArtinMatthews.SpectralPeterssonGammaTail
public import ArtinMatthews.SpectralPeterssonMass
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The incomplete Gamma ratio is exactly the normalized mass of the
literal cut at 4π n y > a, including weight two. -/
noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralPeterssonTruncatedMass_eq (k : ℕ) (hk : 2 ≤ k) (n : ℕ+) (a : ℝ) :
    spectralPeterssonTruncatedMass k n a =
      spectralPeterssonReproducingMass k n*spectralPeterssonGammaTailRatio k a := by
  let r : ℝ := 4*Real.pi*(n : ℝ)
  have hr : 0 < r := by dsimp [r]; positivity
  have hk' : (k-2)+1 = k-1 := by omega
  have hdiv : r*(a/r) = a := by field_simp
  have hscale := integral_comp_mul_left_Ioi
    (fun x : ℝ => x^(k-2)*Real.exp (-x)) (a/r) hr
  rw [hdiv] at hscale
  have hleft : (∫ y in Ioi (a/r), (r*y)^(k-2)*Real.exp (-(r*y))) =
      r^(k-2)*spectralPeterssonTruncatedMass k n a := by
    rw [spectralPeterssonTruncatedMass,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only [r]
    rw [mul_pow]
    ring
  have hmul : r^(k-2)*spectralPeterssonTruncatedMass k n a =
      r⁻¹*spectralPeterssonGammaTail k a := by
    simpa only [hleft,smul_eq_mul,spectralPeterssonGammaTail] using hscale
  have hmass : spectralPeterssonTruncatedMass k n a =
      spectralPeterssonGammaTail k a/r^(k-1) := by
    apply (eq_div_iff (pow_ne_zero _ hr.ne')).mpr
    calc
      _ = r*(r^(k-2)*spectralPeterssonTruncatedMass k n a) := by
        rw [← hk',pow_succ]
        ring
      _ = r*(r⁻¹*spectralPeterssonGammaTail k a) := by rw [hmul]
      _ = _ := by field_simp
  have hG : 0 < Real.Gamma ((k-1 : ℕ) : ℝ) := Real.Gamma_pos_of_pos (by
    exact_mod_cast (show 0 < k-1 by omega))
  rw [hmass,spectralPeterssonReproducingMass,spectralPeterssonGammaTailRatio]
  change spectralPeterssonGammaTail k a/r^(k-1) =
    (Real.Gamma ((k-1 : ℕ) : ℝ)/r^(k-1))*(spectralPeterssonGammaTail k a/Real.Gamma ((k-1 : ℕ) : ℝ))
  field_simp [hG.ne']

theorem spectralPeterssonGammaTailRatio_two (a : ℝ) :
    spectralPeterssonGammaTailRatio 2 a = Real.exp (-a) := by
  have h := integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) a
  unfold spectralPeterssonGammaTailRatio spectralPeterssonGammaTail
  norm_num only [Nat.reduceSub,pow_zero,one_mul,Real.Gamma_one,div_one]
  simpa using h

theorem spectralPeterssonTruncatedMass_lower (k : ℕ) (hk : 2 ≤ k) (n : ℕ+)
    (a : ℝ) (ha : 0 ≤ a) :
    Real.exp (-a)*spectralPeterssonReproducingMass k n ≤ spectralPeterssonTruncatedMass k n a := by
  rw [spectralPeterssonTruncatedMass_eq k hk n a]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (spectralPeterssonGammaTailRatio_bounds k hk a ha).1
    (spectralPeterssonReproducingMass_pos k hk n).le

end ArtinMatthews
