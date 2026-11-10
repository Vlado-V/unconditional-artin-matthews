module

public import ArtinMatthews.ShiftedCommonPrimePart
public import Mathlib.RingTheory.Coprime.Basic
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

/-! Signed complementary factor for the actual common-prime part. -/

namespace ArtinMatthews

theorem exists_commonPrimePart_integer_complement {v : ℤ} (hv : v ≠ 0) (d : ℕ) :
    ∃ A : ℤ, v = (commonPrimePart v.natAbs d : ℤ) * A ∧ IsCoprime (d : ℤ) A := by
  let R := commonPrimePart v.natAbs d
  have hvn : v.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hv
  have hR0 : R ≠ 0 := commonPrimePart_ne_zero hvn d
  have hdvd : (R : ℤ) ∣ v := Int.natCast_dvd.mpr (commonPrimePart_dvd v.natAbs d)
  obtain ⟨A, hA⟩ := hdvd
  refine ⟨A, hA, ?_⟩
  have habs : v.natAbs = R * A.natAbs := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hA
  have hquot : A.natAbs = v.natAbs / R := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hR0)
    rw [Nat.mul_div_cancel' (commonPrimePart_dvd v.natAbs d)]
    exact habs.symm
  have hcop : d.Coprime A.natAbs := by
    rw [hquot]
    exact coprime_commonPrimePart_quotient hvn d
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  simpa only [Int.gcd, Int.natAbs_natCast] using hcop

end ArtinMatthews
