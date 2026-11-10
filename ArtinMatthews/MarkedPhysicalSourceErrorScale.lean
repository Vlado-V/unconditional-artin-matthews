module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

/-! A fixed positive error constant is absorbed before taking the
growing moment root, at the unchanged moment length. -/
namespace ArtinMatthews

theorem markedPhysicalSourceErrorScale {L F G : ℝ} {N : ℕ}
    (hL : 1 ≤ L) (hFL : F ≤ L) (hN : 0 < N) :
    F * L^(-(G+1)*(N:ℝ)) ≤ L^(-G*(N:ℝ)) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hNr : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hP : F ≤ L^(N:ℝ) := hFL.trans (Real.self_le_rpow_of_one_le hL hNr)
  have hp : 0 < L^(N:ℝ) := Real.rpow_pos_of_pos hLp _
  have hs : L^(-(G+1)*(N:ℝ))=L^(-G*(N:ℝ))/(L^(N:ℝ)) := by
    rw [div_eq_mul_inv,← Real.rpow_neg hLp.le,← Real.rpow_add hLp]
    congr 1
    ring
  rw [hs]
  calc
    _ = L^(-G*(N:ℝ))*(F/(L^(N:ℝ))) := by ring
    _ ≤ L^(-G*(N:ℝ))*1 := mul_le_mul_of_nonneg_left ((div_le_one hp).mpr hP)
      (Real.rpow_nonneg hLp.le _)
    _ = _ := mul_one _

end ArtinMatthews
