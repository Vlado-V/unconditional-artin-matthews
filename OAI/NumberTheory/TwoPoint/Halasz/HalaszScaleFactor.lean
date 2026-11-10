module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Normalizing the long/short scale in the classical recurrence.
The loss is a fixed exponential in the moment order. -/
namespace TwoPointCorrelations

lemma halasz_scale_factor {k : ℕ} {x R Q a e : ℝ}
    (hx : 0<x) (hR : 0<R) (hQ : 0≤Q) (he : 0≤e) (hae : e≤a)
    (hRQ : Q≤2*x/R) (hRx : R≤2*x^(1/(k:ℝ))) :
    R^a*x^k*Q^e ≤ 2^a*x^((k:ℝ)+e+(a-e)/(k:ℝ)) := by
  have hbase : 0≤R^a*x^k := mul_nonneg (Real.rpow_nonneg hR.le _) (pow_nonneg hx.le _)
  have hfirst : R^a*x^k*(2*x/R)^e =
      2^e*x^((k:ℝ)+e)*R^(a-e) := by
    rw [Real.div_rpow (by positivity : 0≤2*x) hR.le,
      Real.mul_rpow (by norm_num : (0:ℝ)≤2) hx.le,
      Real.rpow_add hx,Real.rpow_natCast,Real.rpow_sub hR]
    field_simp
  have hlast : 2^e*x^((k:ℝ)+e)*(2*x^(1/(k:ℝ)))^(a-e) =
      2^a*x^((k:ℝ)+e+(a-e)/(k:ℝ)) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hx.le _),
      ← Real.rpow_mul hx.le]
    have htwo : (2:ℝ)^e*2^(a-e)=2^a := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 1
      ring
    have hxexp : (1/(k:ℝ))*(a-e)=(a-e)/(k:ℝ) := by ring
    rw [hxexp]
    calc
      _ = (2^e*2^(a-e))*(x^((k:ℝ)+e)*x^((a-e)/(k:ℝ))) := by ring
      _ = _ := by rw [htwo,← Real.rpow_add hx]
  calc
    _ ≤ R^a*x^k*(2*x/R)^e :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hQ hRQ he) hbase
    _ = 2^e*x^((k:ℝ)+e)*R^(a-e) := hfirst
    _ ≤ 2^e*x^((k:ℝ)+e)*(2*x^(1/(k:ℝ)))^(a-e) := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR.le hRx (sub_nonneg.mpr hae))
      positivity
    _ = _ := hlast

lemma halasz_classical_defect_step (s k : ℕ) (hk : 0<k) (D : ℝ) :
    (k:ℝ)+(2*(s:ℝ)-(k:ℝ)*(k+1)/2+D) +
      ((2*(s:ℝ)+(k:ℝ)*(k-1)/2)-(2*(s:ℝ)-(k:ℝ)*(k+1)/2+D))/(k:ℝ) =
      2*((s:ℝ)+k)-(k:ℝ)*(k+1)/2+(1-1/(k:ℝ))*D := by
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  field_simp
  ring

end TwoPointCorrelations

end OAI
