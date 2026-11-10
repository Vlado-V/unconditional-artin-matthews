module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.TwoPoint.Halasz.HalaszSelectedDoubleMoment
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.NumberTheory.Chebyshev
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
public import OAI.NumberTheory.TwoPoint.Halasz.HalaszDegreeSaving


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! A single absolute saving exponent covers the bounded-degree cases. -/
namespace TwoPointCorrelations

lemma halasz_bounded_root_saving {k : ℕ} (hk : 2≤k) (hkhi : k≤150)
    {lam : ℝ} (hlam : 49/100≤lam) :
    1/((10^15:ℝ)*lam^2) ≤
      (1/32:ℝ)/((2*halaszSelectedMoment k*halaszSelectedMoment k:ℕ):ℝ) := by
  have hk0 : 0≤(k:ℝ) := Nat.cast_nonneg _
  have hkR : (k:ℝ)≤150 := by exact_mod_cast hkhi
  have hk2 : (k:ℝ)^2≤150^2 := pow_le_pow_left₀ hk0 hkR 2
  have hr : (halaszSelectedMoment k:ℝ)≤225150 := by
    simp only [halaszSelectedMoment,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    nlinarith
  have hr0 : 0<(halaszSelectedMoment k:ℝ) := by
    exact_mod_cast (show 0<halaszSelectedMoment k from
      lt_of_lt_of_le Nat.zero_lt_one (halasz_selected_moment_pos hk))
  have hr2 := pow_le_pow_left₀ hr0.le hr 2
  have hp : 0<((2*halaszSelectedMoment k*halaszSelectedMoment k:ℕ):ℝ) := by
    push_cast
    positivity
  have hlam0 : 0<lam := by linarith
  have hlam2 : (49/100:ℝ)^2≤lam^2 := pow_le_pow_left₀ (by norm_num) hlam 2
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<10^15*lam^2) hp).mpr
  push_cast
  nlinarith

lemma halasz_low_degree_saving {lam : ℝ} (hlo : 49/100≤lam) (hhi : lam≤9/10) :
    (1:ℝ)/32+(6:ℝ)^2/1024≤min (1/3:ℝ) (min (1-lam) (lam-1/3)) := by
  have hh := halasz_low_height_degree_margin hlo hhi
  linarith

end TwoPointCorrelations

end OAI
