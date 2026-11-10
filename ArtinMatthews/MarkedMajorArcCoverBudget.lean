module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Absorption of the actual finite-major-cover measure cost. -/
namespace ArtinMatthews

 theorem markedMajor_cover_cost {L a P Y X Q : ℝ}
    (hL : 4 ≤ L) (hQ : 0 ≤ Q) (hQa : Q ≤ L^a) (hY : 0 ≤ Y) (hX : 0 ≤ X) :
    4*Q^3*((Y*X)*L^(-(P+3*a+1))) ≤ (Y*X)*L^(-P) := by
  have hLp : 0 < L := by linarith
  have hQ3 : Q^3 ≤ L^(3*a) := by
    calc
      _ ≤ (L^a)^3 := pow_le_pow_left₀ hQ hQa 3
      _ = L^(3*a) := by simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hLp.le a 3).symm
  have he : 4*L^(3*a)*L^(-(P+3*a+1)) = (4/L)*L^(-P) := by
    rw [mul_assoc,← Real.rpow_add hLp]
    have hp : 3*a+ -(P+3*a+1)= -P+(-1) := by ring
    rw [hp,Real.rpow_add hLp,Real.rpow_neg_one]
    ring
  calc
    _ ≤ 4*L^(3*a)*((Y*X)*L^(-(P+3*a+1))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ3 (by norm_num))
        (mul_nonneg (mul_nonneg hY hX) (Real.rpow_nonneg hLp.le _))
    _ = (Y*X)*((4/L)*L^(-P)) := by rw [← he]; ring
    _ ≤ (Y*X)*(1*L^(-P)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        ((div_le_one hLp).mpr hL) (Real.rpow_nonneg hLp.le _)) (mul_nonneg hY hX)
    _ = _ := by rw [one_mul]

end ArtinMatthews
