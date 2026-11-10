module

public import ArtinMatthews.CubicThetaBesselSquareAll
public import ArtinMatthews.ShiftedDualZeroKloosterman
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Absolute control of the actual zero-frequency theta/Bessel term. The
Kloosterman factor is reduced to its Ramanujan diagonal; no spectral estimate
is used to dispose of this term. -/

noncomputable section
open Set OAI
namespace ArtinMatthews

theorem thetaDualZero_bessel_bound (ε : ℝ) (hε : 0 < ε) (hεtwo : ε ≤ 2) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (χ : SevenEighths.HeckeFamily.Character) (W1 W2 : SchwartzMap ℝ ℂ)
        (B1 B2 : ℝ), 0 ≤ B1 → 0 ≤ B2 →
        Function.support W1 ⊆ Icc 0 B1 → Function.support W2 ⊆ Icc 0 B2 →
      ∀ (K1 K2 : ℝ), 0 < K1 → 0 < K2 →
      ∀ (q D m3 m4 : ℕ) [NeZero q], 0 < m3 → 0 < m4 → m3 ≠ m4 →
      Summable (shiftedDualZeroTerm q D m3 m4
        (thetaBesselCoeff χ W1 K1 ((q : ℝ)^2)) (thetaBesselCoeff χ W2 K2 ((q : ℝ)^2))) ∧
      ‖∑' k, shiftedDualZeroTerm q D m3 m4
        (thetaBesselCoeff χ W1 K1 ((q : ℝ)^2)) (thetaBesselCoeff χ W2 K2 ((q : ℝ)^2)) k‖ ≤
        ((((m3 : ℤ) - m4).natAbs : ℝ)^2 * C / 2) *
          (K1^2 * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W1)^2 * (((q : ℝ)^2) / K1)^(1 + ε) +
           K2^2 * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W2)^2 * (((q : ℝ)^2) / K2)^(1 + ε)) := by
  obtain ⟨s, C, hC, hbound⟩ := thetaBesselCoeff_square_bound ε hε hεtwo
  refine ⟨s, C, hC, ?_⟩
  intro χ W1 W2 B1 B2 hB1 hB2 hW1 hW2 K1 K2 hK1 hK2 q D m3 m4 inst hm3 hm4 hne
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  obtain ⟨hs1, hb1⟩ := hbound χ W1 B1 hB1 hW1 K1 ((q : ℝ)^2) hK1 (sq_pos_of_pos hq)
  obtain ⟨hs2, hb2⟩ := hbound χ W2 B2 hB2 hW2 K2 ((q : ℝ)^2) hK2 (sq_pos_of_pos hq)
  obtain ⟨hs, hb⟩ := shiftedDualZeroTerm_summable_bound q D m3 m4 hm3 hm4 hne
    (thetaBesselCoeff χ W1 K1 ((q : ℝ)^2)) (thetaBesselCoeff χ W2 K2 ((q : ℝ)^2)) hs1 hs2
  refine ⟨hs, hb.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (add_le_add hb1 hb2) (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg ((((m3 : ℤ) - m4).natAbs : ℝ)))
  convert h using 1
  ring

end ArtinMatthews
