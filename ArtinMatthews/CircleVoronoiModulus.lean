module

public import ArtinMatthews.CircleShiftedFrequency
public import ArtinMatthews.ShiftedCommonPrimePartSquarefree
public import ArtinMatthews.ShiftedDoubleVoronoiFubini
public import ArtinMatthews.CircleVoronoiBridge
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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

/-! A modulus-indexed form of the exact double Voronoi identity. The zero
modulus is assigned zero only to make finite averaging a total function. -/

noncomputable section
open Complex UpperHalfPlane Set
open scoped MatrixGroups ContDiff BigOperators
open OAI.Erdos970.ErdosKloosterman
namespace ArtinMatthews

def circleVoronoiDual (N : ℕ) [NeZero N]
    (f : CuspForm (cubicThetaKernel N) 1) (m1 m2 q : ℕ) (H1 H2 : ℝ → ℂ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    let d := m1.gcd m2
    let m3 := m1 / d
    let m4 := m2 / d
    (cubicThetaNebentypus (-((m3 : ℕ) : ℤ) * m4) / (q : ℂ)^2) *
      ∑' k : ℕ × ℕ, cuspBesselPair f q H1 H2 k *
        ((if Int.ModEq (shiftedCommonPrimePart m1 m2 : ℤ)
          ((m3 : ℤ)^2 * k.1) ((m4 : ℤ)^2 * k.2) then 1 else 0) *
          sum ZMod.stdAddChar ((m3 : ZMod q) - (m4 : ZMod q))
            (((m3 : ZMod q) * (m4 : ZMod q))⁻¹ *
              ((m4 : ZMod q) * k.2 - (m3 : ZMod q) * k.1)))

theorem circle_weightOne_voronoi_modulus
    (N : ℕ) [NeZero N] (hN : 3 ∣ N) (f : CuspForm (cubicThetaKernel N) 1)
    (m1 m2 q K1 K2 : ℕ) (hq : 0 < q)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hne : m1 ≠ m2)
    (hsq1 : Squarefree m1) (hsq2 : Squarefree m2)
    (hQ : N * (shiftedCommonPrimePart m1 m2)^2 ∣ q)
    (hc : ((m1 / (m1.gcd m2)) * (m2 / (m1.gcd m2))).Coprime q)
    (H1 H2 : ℝ → ℂ) (hs1 : ContDiff ℝ ∞ H1) (hs2 : ContDiff ℝ ∞ H2)
    (u1 v1 u2 v2 : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hv1 : v1 ≤ K1) (hv2 : v2 ≤ K2)
    (hw1 : Function.support H1 ⊆ Icc u1 v1) (hw2 : Function.support H2 ⊆ Icc u2 v2) :
    (∑ k ∈ (Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2),
      cuspSourcePair f H1 H2 k * primitiveCircleSum q
        (circleShiftedFrequency (m1 / (m1.gcd m2)) (m2 / (m1.gcd m2)) k) *
        (if ((m1.gcd m2) : ℤ) ∣ ((k.1 : ℤ) - 1) then 1 else 0)) =
      circleVoronoiDual N f m1 m2 q H1 H2 := by
  let d := m1.gcd m2
  have hd : 0 < d := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m1 m2) hm1
  let : NeZero d := ⟨hd.ne'⟩
  obtain ⟨R, A, hR, hD, hfactor, hcop, hcop1, hcop2⟩ :=
    squarefree_commonPrimePart_factors hm1 hm2 hne hsq1 hsq2
  have hdq : d ∣ q := by
    apply (show d ∣ N * (shiftedCommonPrimePart m1 m2)^2 from ?_).trans hQ
    rw [hD]
    exact ⟨N * d * R^2, by ring⟩
  have hmul : (q / d) * d = q := Nat.div_mul_cancel hdq
  have hmul' : (q / d) * (m1.gcd m2) = q := hmul
  have hH : 0 < q / d := by nlinarith
  let : NeZero (q / d) := ⟨hH.ne'⟩
  have hv := circle_weightOne_voronoi_squarefree N hN f m1 m2 (q / d) K1 K2
    hm1 hm2 hne hsq1 hsq2 (by simpa only [hmul'] using hQ)
    (by simpa only [hmul'] using hc)
    H1 H2 hs1 hs2 u1 v1 u2 v2 hu1 hu2 hv1 hv2 hw1 hw2
  dsimp only at hv
  have hi :
      (∑ k ∈ (Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2),
        cuspSourcePair f H1 H2 k * primitiveCircleSum ((q / d) * (m1.gcd m2))
          (circleShiftedFrequency (m1 / (m1.gcd m2)) (m2 / (m1.gcd m2)) k) *
          (if ((m1.gcd m2) : ℤ) ∣ ((k.1 : ℤ) - 1) then 1 else 0)) =
        circleVoronoiDual N f m1 m2 ((q / d) * (m1.gcd m2)) H1 H2 := by
    simpa only [circleVoronoiDual, dite_eq_right (by omega : (q / d) * (m1.gcd m2) ≠ 0),
      ← ZMod.inv_coe_unit, Units.val_mul, ZMod.coe_unitOfCoprime] using hv
  simpa only [hmul'] using hi

end ArtinMatthews
