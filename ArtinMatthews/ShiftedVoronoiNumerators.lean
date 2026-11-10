module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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

/-! The two additive numerators in the double Voronoi step are units.
Divisibility by d² makes the correction term square-zero modulo q. -/

namespace ArtinMatthews

theorem div_square_dvd_of_square_dvd {q d : ℕ} (hd : 0 < d) (hdd : d^2 ∣ q) :
    q ∣ (q/d)^2 := by
  obtain ⟨c, rfl⟩ := hdd
  have hquot : d^2*c/d = d*c := by
    rw [pow_two, mul_assoc, Nat.mul_div_cancel_left _ hd]
  rw [hquot]
  exact ⟨c, by ring⟩

/-- Literal correction appearing after the d-congruence average. -/
theorem doubleVoronoi_correction_isUnit {q d : ℕ} (hd : 0 < d) (hdd : d^2 ∣ q)
    (j : ℤ) : IsUnit (1 + (j : ZMod q)*(q/d : ℕ)) := by
  have hp : ((q/d : ℕ) : ZMod q)^2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact div_square_dvd_of_square_dvd hd hdd
  have hn : IsNilpotent ((j : ZMod q)*(q/d : ℕ)) :=
    ⟨2, by rw [mul_pow, hp, mul_zero]⟩
  exact hn.isUnit_one_add

/-- The nilpotent correction has the exact inverse used in the dual
additive phase; this holds for composite circle moduli as well. -/
theorem doubleVoronoi_correction_inv {q d : ℕ} (hd : 0 < d) (hdd : d^2 ∣ q)
    (j : ℤ) : (1+(j : ZMod q)*(q/d : ℕ))⁻¹ = 1-(j : ZMod q)*(q/d : ℕ) := by
  apply ZMod.inv_eq_of_mul_eq_one
  have hp : ((q/d : ℕ) : ZMod q)^2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact div_square_dvd_of_square_dvd hd hdd
  calc
    _ = 1-(j : ZMod q)^2*((q/d : ℕ) : ZMod q)^2 := by ring
    _ = 1 := by rw [hp, mul_zero, sub_zero]

/-- Both numerators in paper (5.7), with the ordinary coprimality
assumptions and the actual q/d correction. -/
theorem doubleVoronoi_numerators_isUnit {q d a m₃ m₄ : ℕ}
    (hd : 0 < d) (hdd : d^2 ∣ q) (ha : a.Coprime q)
    (hm : (m₃*m₄).Coprime q) (j : ℤ) :
    IsUnit ((m₄ : ZMod q)*a*(1+(j : ZMod q)*(q/d : ℕ))) ∧
    IsUnit (-(m₃ : ZMod q)*a) := by
  have ha' := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hm' := (ZMod.isUnit_iff_coprime (m₃*m₄) q).mpr hm
  have hm'' : IsUnit ((m₃ : ZMod q)*m₄) := by simpa only [Nat.cast_mul] using hm'
  have h₃ := isUnit_of_mul_isUnit_left hm''
  have h₄ := isUnit_of_mul_isUnit_right hm''
  exact ⟨(h₄.mul ha').mul (doubleVoronoi_correction_isUnit hd hdd j), h₃.neg.mul ha'⟩

end ArtinMatthews
