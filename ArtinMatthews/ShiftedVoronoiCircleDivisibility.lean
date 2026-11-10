module

public import ArtinMatthews.ShiftedVoronoiCharacter
public import ArtinMatthews.ShiftedVoronoiCharacterProduct
public import ArtinMatthews.ShiftedVoronoiNumerators
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Data.Nat.Choose.Multinomial
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual circle modulus ND² supplies both the nilpotence and
nebentypus conductor divisibility required in the double transformation. -/

namespace ArtinMatthews

theorem circleModulus_divisibilities {N D d q : ℕ}
    (hdD : d ∣ D) (hQ : N*D^2 ∣ q) :
    d ∣ q ∧ d^2 ∣ q ∧ N ∣ q/d := by
  have hD2 : D^2 ∣ N*D^2 := ⟨N, by ring⟩
  have hdD2 : d ∣ D^2 := hdD.trans ⟨D, by ring⟩
  have hdq : d ∣ q := hdD2.trans (hD2.trans hQ)
  refine ⟨hdq, (pow_dvd_pow_of_dvd hdD 2).trans (hD2.trans hQ), ?_⟩
  apply (Nat.dvd_div_iff_mul_dvd hdq).mpr
  have hn := (Nat.mul_dvd_mul_left N hdD2).trans hQ
  simpa only [Nat.mul_comm d N] using hn

/-- Complete numerator and character arithmetic at the prescribed circle
moduli, independent of the circle numerator and d-congruence class. -/
theorem doubleVoronoi_circle_arithmetic {N D d q a m₃ m₄ : ℕ}
    (hd : 0 < d) (hdD : d ∣ D) (hQ : N*D^2 ∣ q) (hN : 3 ∣ N)
    (ha : a.Coprime q) (hm : (m₃*m₄).Coprime q) (j : ℤ) :
    (IsUnit ((m₄ : ZMod q)*a*(1+(j : ZMod q)*(q/d : ℕ))) ∧
      IsUnit (-(m₃ : ZMod q)*a)) ∧
    cubicThetaNebentypus ((m₄ : ℤ)*a*(1+j*(q/d : ℕ))) *
      cubicThetaNebentypus (-(m₃ : ℤ)*a) = cubicThetaNebentypus (-(m₃ : ℤ)*m₄) := by
  obtain ⟨hdq,hdd,hquot⟩ := circleModulus_divisibilities hdD hQ
  exact ⟨doubleVoronoi_numerators_isUnit hd hdd ha hm j,
    doubleVoronoi_character_product hdq (hN.trans hquot) ha m₃ m₄ j⟩

end ArtinMatthews
