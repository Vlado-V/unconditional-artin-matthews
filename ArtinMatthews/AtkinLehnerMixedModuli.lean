module

public import ArtinMatthews.AtkinLehnerMixedArithmetic
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

/-! Actual allowable mixed-cusp moduli and their necessary coprimality. -/
namespace ArtinMatthews

open Matrix CongruenceSubgroup

theorem atkinMixedSL_lower {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (A B c D : ℤ)
    (hdet : (r : ℤ)*A*D-(s : ℤ)*c*B = 1) :
    (atkinMixedSL hr hab A B c D hdet) 1 0 =
      (s : ℝ)*Real.sqrt (r : ℝ)*(c : ℝ) := by
  rw [atkinMixedSL_coe]
  change (1/Real.sqrt (r : ℝ))*(((r : ℤ)*(s : ℤ)*c : ℤ) : ℝ) = _
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have ht : Real.sqrt (r : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hrR).ne'
  push_cast
  field_simp [ht]
  linear_combination -(s : ℝ)*(c : ℝ)*(Real.sq_sqrt hrR.le)

/-- The mixed determinant constraint forces precisely the coprimality used in
the ordinary inverse-r Kloosterman parameterization. -/
theorem atkinMixed_constraint_coprime {r s : ℕ} {A B c D : ℤ}
    (hdet : (r : ℤ)*A*D-(s : ℤ)*c*B = 1) : r.Coprime c.natAbs := by
  have hi : IsCoprime (r : ℤ) c := by
    refine ⟨A*D,-(s : ℤ)*B,?_⟩
    linear_combination hdet
  have hg := Int.isCoprime_iff_gcd_eq_one.mp hi
  simpa only [Int.gcd,Int.natAbs_natCast] using hg

/-- Literal definition through the actual mixed Gamma0-times-scaling coset. -/
def atkinMixedAllowed {r s : ℕ} (hr : 0 < r) {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (γc : ℝ) : Prop :=
  0 < γc ∧ ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Gamma0 (r*s) ∧
    (atkinRealMap γ * atkinScaling hr hab) 1 0 = γc

/-- All and only the positive `s*sqrt(r)*c` with `(c,r)=1` occur. The
quantified integer parameter is obtained from actual integral matrix entries. -/
theorem atkinMixedAllowed_iff {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hrs : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (γc : ℝ) :
    atkinMixedAllowed hr hab γc ↔
      ∃ c : ℤ, 0 < c ∧ r.Coprime c.natAbs ∧ γc = (s : ℝ)*Real.sqrt (r : ℝ)*(c : ℝ) := by
  have ht : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hr)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hscale : 0 < (s : ℝ)*Real.sqrt (r : ℝ) := mul_pos hsR ht
  constructor
  · rintro ⟨hγc,γ,hγ,hentry⟩
    obtain ⟨A,B,c,D,hdet,heq⟩ := atkinMixedSL_parameterization hr hab γ hγ
    have hc := atkinMixedSL_lower hr hab A B c D hdet
    rw [heq,hentry] at hc
    have hcR : (0 : ℝ) < c := by
      by_contra hh
      have hcn : (c : ℝ) ≤ 0 := le_of_not_gt hh
      have := mul_nonpos_of_nonneg_of_nonpos hscale.le hcn
      rw [← hc] at this
      linarith
    exact ⟨c,by exact_mod_cast hcR,atkinMixed_constraint_coprime hdet,hc⟩
  · rintro ⟨c,hc,hrc,rfl⟩
    have hrsI : IsCoprime (r : ℤ) (s : ℤ) := hrs.isCoprime
    have hrcI : IsCoprime (r : ℤ) c := by
      apply Int.isCoprime_iff_gcd_eq_one.mpr
      simpa only [Int.gcd,Int.natAbs_natCast] using hrc.gcd_eq_one
    obtain ⟨D,B,hDB⟩ := hrsI.mul_right hrcI
    have hdet : (r : ℤ)*1*D-(s : ℤ)*c*(-B) = 1 := by linear_combination hDB
    refine ⟨mul_pos hscale (by exact_mod_cast hc),
      atkinMixedPreimageSL r s a b 1 (-B) c D hab hdet,
      atkinMixedPreimageSL_mem r s a b 1 (-B) c D hab hdet,?_⟩
    exact atkinMixedSL_lower hr hab 1 (-B) c D hdet

theorem atkinMixedAllowed_nat_scale_iff {r s c : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hrs : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1) :
    atkinMixedAllowed hr hab ((s : ℝ)*Real.sqrt (r : ℝ)*(c : ℝ)) ↔ 0 < c ∧ c.Coprime r := by
  rw [atkinMixedAllowed_iff hr hs hrs hab]
  have hscale : (s : ℝ)*Real.sqrt (r : ℝ) ≠ 0 :=
    (mul_pos (by exact_mod_cast hs) (Real.sqrt_pos.mpr (by exact_mod_cast hr))).ne'
  constructor
  · rintro ⟨k,hk,hcop,heq⟩
    have hkc : (c : ℝ) = (k : ℝ) := mul_left_cancel₀ hscale heq
    have hki : (c : ℤ) = k := by exact_mod_cast hkc
    rw [← hki] at hk hcop
    rw [Int.natAbs_natCast] at hcop
    exact ⟨by exact_mod_cast hk,hcop.symm⟩
  · rintro ⟨hc,hcop⟩
    exact ⟨(c : ℤ),by exact_mod_cast hc,by simpa only [Int.natAbs_natCast] using hcop.symm,rfl⟩

end ArtinMatthews
