module

public import ArtinMatthews.ShiftedDoubleVoronoiFubini
public import ArtinMatthews.DoubleVoronoiDetection
public import ArtinMatthews.ShiftedDoubleVoronoi
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

/-! The analytic double transformation with the actual detector phase.
The constant phase is retained, and the exact source and dual raw phases are
those in the independently proved finite arithmetic. -/

noncomputable section
open Complex UpperHalfPlane Set Finset
open scoped MatrixGroups ContDiff
open OAI.Erdos970.ErdosKloosterman.PrimePower

namespace ArtinMatthews

/-- Multiplying a coefficient series by a constant additive character shifts
its phase exactly. Summability of the concrete series is proved separately. -/
theorem tsum_stdAddChar_shift {ι : Type*} (q : ℕ) [NeZero q]
    (A : ι → ℂ) (c : ZMod q) (P : ι → ZMod q) :
    ZMod.stdAddChar c * (∑' k : ι, A k * ZMod.stdAddChar (P k)) =
      ∑' k : ι, A k * ZMod.stdAddChar (c + P k) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [AddChar.map_add_eq_mul]
  ring

set_option maxHeartbeats 800000 in
/-- Exact double Voronoi at each numerator and congruence character, including
the constant detector phase. The actual level and divisibility assumptions
supply both the character scalar and all numerator-unit conditions. -/
theorem weightOne_double_voronoi_detector
    (N : ℕ) [NeZero N] (hN : 3∣N) (f : CuspForm (cubicThetaKernel N) 1)
    (D H d : ℕ) [NeZero H] [NeZero d]
    (hdH : d∣H) (hdD : d∣D) (hQ : N*D^2∣H*d)
    (m3 m4 : ℕ) (v3 v4 : (ZMod (H*d))ˣ)
    (hv3 : (v3 : ZMod (H*d))=(m3 : ZMod (H*d)))
    (hv4 : (v4 : ZMod (H*d))=(m4 : ZMod (H*d)))
    (a : (ZMod (H*d))ˣ) (j : ZMod d)
    (H1 H2 : ℝ → ℂ) (hs1 : ContDiff ℝ ∞ H1) (hs2 : ContDiff ℝ ∞ H2)
    (u1 v1 u2 v2 : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hw1 : Function.support H1 ⊆ Icc u1 v1) (hw2 : Function.support H2 ⊆ Icc u2 v2) :
    (∑' k : ℕ × ℕ, cuspSourcePair f H1 H2 k *
      ZMod.stdAddChar (doubleVoronoiPrimalPhase H d hdH v3 v4 a k.1 k.2 j)) =
      (cubicThetaNebentypus (-(m3 : ℤ)*m4) / ((H*d : ℕ) : ℂ)^2) *
        ∑' k : ℕ × ℕ, cuspBesselPair f (H*d) H1 H2 k *
          ZMod.stdAddChar (doubleVoronoiDualPhase H d hdH v3 v4 a k.1 k.2 j) := by
  have hm : (m3*m4).Coprime (H*d) := by
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · exact (ZMod.isUnit_iff_coprime m3 (H*d)).mp (hv3 ▸ v3.isUnit)
    · exact (ZMod.isUnit_iff_coprime m4 (H*d)).mp (hv4 ▸ v4.isUnit)
  let h : ZMod (H*d) := (H : ZMod (H*d))*(j.val : ZMod (H*d))
  let U1 := v4*a*shiftUnit 1 h (circleCorrection_square_zero H d hdH j)
  let U2 := -(v3*a)
  let c : ZMod (H*d) := ((v3 : ZMod (H*d))-(v4 : ZMod (H*d)))*(a : ZMod (H*d)) -
    h*(v4 : ZMod (H*d))*(a : ZMod (H*d))
  have hn1 : (m4 : ZMod (H*d))*(a : ZMod (H*d)) *
      (1+(j.val : ZMod (H*d))*(H : ZMod (H*d))) = (U1 : ZMod (H*d)) := by
    simp only [U1, Units.val_mul, shiftUnit_val, Units.val_one, h, hv4]
    ring
  have hn2 : -(m3 : ZMod (H*d))*(a : ZMod (H*d)) = (U2 : ZMod (H*d)) := by
    simp only [U2, Units.val_neg, Units.val_mul, hv3]
    ring
  have hx := weightOne_double_voronoi_circle N hN f D d (H*d) (a : ZMod (H*d)).val m3 m4
    (NeZero.pos d) hdD hQ (ZMod.val_coe_unit_coprime a) hm (j.val : ℤ)
    H1 H2 hs1 hs2 u1 v1 u2 v2 hu1 hu2 hw1 hw2
  simp only [Nat.mul_div_cancel H (NeZero.pos d), Int.cast_natCast,
    ZMod.natCast_zmod_val, hn1, hn2, ZMod.inv_coe_unit] at hx
  have hx' : (∑' k : ℕ × ℕ, cuspSourcePair f H1 H2 k *
      ZMod.stdAddChar ((U1 : ZMod (H*d))*(k.1 : ZMod (H*d)) + (U2 : ZMod (H*d))*(k.2 : ZMod (H*d)))) =
      (cubicThetaNebentypus (-(m3 : ℤ)*m4) / ((H*d : ℕ) : ℂ)^2) *
        ∑' k : ℕ × ℕ, cuspBesselPair f (H*d) H1 H2 k *
          ZMod.stdAddChar (-(↑U1⁻¹ : ZMod (H*d))*(k.1 : ZMod (H*d)) + -(↑U2⁻¹ : ZMod (H*d))*(k.2 : ZMod (H*d))) := by
    convert hx using 1
    · apply tsum_congr
      intro k
      unfold cuspSourcePair
      ring
    · congr 1
      apply tsum_congr
      intro k
      unfold cuspBesselPair cuspSourcePair
      ring
  have hy := congrArg (fun z : ℂ ↦ ZMod.stdAddChar c * z) hx'
  rw [tsum_stdAddChar_shift] at hy
  rw [mul_left_comm (ZMod.stdAddChar c), tsum_stdAddChar_shift] at hy
  convert hy using 1
  · apply tsum_congr
    intro k
    congr 2
    dsimp [doubleVoronoiPrimalPhase, U1, U2, c, h]
    ring
  · congr 1
    apply tsum_congr
    intro k
    congr 2
    dsimp [doubleVoronoiDualPhase, U1, U2, c, h]
    ring

end ArtinMatthews
