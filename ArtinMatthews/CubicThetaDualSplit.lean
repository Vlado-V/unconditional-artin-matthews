module

public import ArtinMatthews.ShiftedDualSplit
public import ArtinMatthews.CubicThetaDualZeroAverage
public import ArtinMatthews.CubicThetaBesselSummable
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Split the actual theta Bessel dual sum into its zero and nonzero integer
frequencies, and control the difference of the corresponding circle averages. -/

noncomputable section
open Set OAI
open scoped BigOperators
namespace ArtinMatthews

def thetaDualNormalized (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ) (D m3 m4 q : ℕ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (cubicThetaNebentypus (-((m3 : ℕ) : ℤ) * m4) / (q : ℂ)^2) *
      ∑' k, shiftedDualTerm q D m3 m4
        (thetaBesselCoeff χ W1 K1 ((q : ℝ)^2)) (thetaBesselCoeff χ W2 K2 ((q : ℝ)^2)) k

def thetaDualNonzeroNormalized (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ) (D m3 m4 q : ℕ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (cubicThetaNebentypus (-((m3 : ℕ) : ℤ) * m4) / (q : ℂ)^2) *
      ∑' k, shiftedDualNonzeroTerm q D m3 m4
        (thetaBesselCoeff χ W1 K1 ((q : ℝ)^2)) (thetaBesselCoeff χ W2 K2 ((q : ℝ)^2)) k

theorem thetaDualNormalized_split (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (B1 B2 : ℝ) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hW1 : Function.support W1 ⊆ Icc 0 B1) (hW2 : Function.support W2 ⊆ Icc 0 B2)
    (K1 K2 : ℝ) (hK1 : 0 < K1) (hK2 : 0 < K2) (D m3 m4 q : ℕ) :
    thetaDualNormalized χ W1 W2 K1 K2 D m3 m4 q =
      thetaDualZeroNormalized χ W1 W2 K1 K2 D m3 m4 q +
        thetaDualNonzeroNormalized χ W1 W2 K1 K2 D m3 m4 q := by
  by_cases hq : q = 0
  · simp only [thetaDualNormalized, thetaDualZeroNormalized, thetaDualNonzeroNormalized,
      dite_eq_left hq, add_zero]
  · let : NeZero q := ⟨hq⟩
    have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    simp only [thetaDualNormalized, thetaDualZeroNormalized, thetaDualNonzeroNormalized,
      dite_eq_right hq]
    rw [shiftedDualSum_split q D m3 m4 _ _
      (thetaBesselCoeff_summable χ W1 B1 hB1 hW1 K1 _ hK1 (by positivity))
      (thetaBesselCoeff_summable χ W2 B2 hB2 hW2 K2 _ hK2 (by positivity)), mul_add]

def thetaDualCircleAverage (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ) (D m3 m4 F r L : ℕ) : ℂ :=
  (∑ q ∈ circleModuli F r L, (circleSmoothWeight L q : ℂ) *
    thetaDualNormalized χ W1 W2 K1 K2 D m3 m4 q) /
      (circleNormalizer (circleModuli F r L) (circleSmoothWeight L) : ℂ)

def thetaDualNonzeroCircleAverage (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ) (D m3 m4 F r L : ℕ) : ℂ :=
  (∑ q ∈ circleModuli F r L, (circleSmoothWeight L q : ℂ) *
    thetaDualNonzeroNormalized χ W1 W2 K1 K2 D m3 m4 q) /
      (circleNormalizer (circleModuli F r L) (circleSmoothWeight L) : ℂ)

theorem thetaDualCircleAverage_split (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (B1 B2 : ℝ) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hW1 : Function.support W1 ⊆ Icc 0 B1) (hW2 : Function.support W2 ⊆ Icc 0 B2)
    (K1 K2 : ℝ) (hK1 : 0 < K1) (hK2 : 0 < K2) (D m3 m4 F r L : ℕ) :
    thetaDualCircleAverage χ W1 W2 K1 K2 D m3 m4 F r L =
      thetaDualZeroCircleAverage χ W1 W2 K1 K2 D m3 m4 F r L +
        thetaDualNonzeroCircleAverage χ W1 W2 K1 K2 D m3 m4 F r L := by
  unfold thetaDualCircleAverage thetaDualZeroCircleAverage thetaDualNonzeroCircleAverage
  simp_rw [thetaDualNormalized_split χ W1 W2 B1 B2 hB1 hB2 hW1 hW2 K1 K2 hK1 hK2]
  simp only [mul_add, Finset.sum_add_distrib, add_div]

theorem thetaDualCircleAverage_nonzero_error :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (χ : SevenEighths.HeckeFamily.Character) (W1 W2 : SchwartzMap ℝ ℂ)
        (B1 B2 : ℝ), 0 ≤ B1 → 0 ≤ B2 →
        Function.support W1 ⊆ Icc 0 B1 → Function.support W2 ⊆ Icc 0 B2 →
      ∀ (K1 K2 : ℝ), 0 < K1 → 0 < K2 →
      ∀ (D m3 m4 : ℕ), 0 < m3 → 0 < m4 → m3 ≠ m4 →
      ∀ (F r L : ℕ), 0 < F → 0 < r → F.Coprime r → 4 * (F * r) ≤ L →
      ‖thetaDualCircleAverage χ W1 W2 K1 K2 D m3 m4 F r L -
          thetaDualNonzeroCircleAverage χ W1 W2 K1 K2 D m3 m4 F r L‖ ≤
        C * (((m3 : ℤ) - m4).natAbs : ℝ)^2 *
          (K1^(7/8 : ℝ) * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W1)^2 +
           K2^(7/8 : ℝ) * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W2)^2) *
          (F : ℝ) * (r : ℝ)^(1/4 : ℝ) / Real.sqrt L := by
  obtain ⟨s, C, hC, hbound⟩ := thetaDualZeroCircleAverage_bound
  refine ⟨s, C, hC, ?_⟩
  intro χ W1 W2 B1 B2 hB1 hB2 hW1 hW2 K1 K2 hK1 hK2 D m3 m4 hm3 hm4 hne F r L hF hr hFr hL
  rw [thetaDualCircleAverage_split χ W1 W2 B1 B2 hB1 hB2 hW1 hW2 K1 K2 hK1 hK2,
    add_sub_cancel_right]
  exact hbound χ W1 W2 B1 B2 hB1 hB2 hW1 hW2 K1 K2 hK1 hK2 D m3 m4 hm3 hm4 hne F r L hF hr hFr hL

end ArtinMatthews
