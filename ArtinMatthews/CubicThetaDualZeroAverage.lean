module

public import ArtinMatthews.CubicThetaDualZeroNormalized
public import ArtinMatthews.CircleDetector
public import ArtinMatthews.CircleNormalizerDefinitions
public import ArtinMatthews.CircleNormalizerSmooth
public import ArtinMatthews.CircleQuarterGrowth
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

/-! The actual normalized zero dual-frequency contribution tends to zero at
a power rate under the same smooth all-moduli average used in Voronoi. -/

noncomputable section
open Set OAI
open scoped BigOperators
namespace ArtinMatthews

def thetaDualZeroCircleAverage (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ) (D m3 m4 F r L : ℕ) : ℂ :=
  (∑ q ∈ circleModuli F r L, (circleSmoothWeight L q : ℂ) *
    thetaDualZeroNormalized χ W1 W2 K1 K2 D m3 m4 q) /
      (circleNormalizer (circleModuli F r L) (circleSmoothWeight L) : ℂ)

theorem thetaDualZeroCircleAverage_bound :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (χ : SevenEighths.HeckeFamily.Character) (W1 W2 : SchwartzMap ℝ ℂ)
        (B1 B2 : ℝ), 0 ≤ B1 → 0 ≤ B2 →
        Function.support W1 ⊆ Icc 0 B1 → Function.support W2 ⊆ Icc 0 B2 →
      ∀ (K1 K2 : ℝ), 0 < K1 → 0 < K2 →
      ∀ (D m3 m4 : ℕ), 0 < m3 → 0 < m4 → m3 ≠ m4 →
      ∀ (F r L : ℕ), 0 < F → 0 < r → F.Coprime r → 4 * (F * r) ≤ L →
      ‖thetaDualZeroCircleAverage χ W1 W2 K1 K2 D m3 m4 F r L‖ ≤
        C * (((m3 : ℤ) - m4).natAbs : ℝ)^2 *
          (K1^(7/8 : ℝ) * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W1)^2 +
           K2^(7/8 : ℝ) * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W2)^2) *
          (F : ℝ) * (r : ℝ)^(1/4 : ℝ) / Real.sqrt L := by
  obtain ⟨s, Cn, hCn, hnorm⟩ := thetaDualZeroNormalized_bound (1/8) (by norm_num) (by norm_num)
  obtain ⟨Ca, hCa, havg⟩ := circleAverage_quarter_growth
  refine ⟨s, Ca * Cn / 2, by positivity, ?_⟩
  intro χ W1 W2 B1 B2 hB1 hB2 hW1 hW2 K1 K2 hK1 hK2 D m3 m4 hm3 hm4 hne F r L hF hr hFr hL
  let V : ℝ := ((((m3 : ℤ) - m4).natAbs : ℝ)^2 * Cn / 2) *
    (K1^(7/8 : ℝ) * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W1)^2 +
     K2^(7/8 : ℝ) * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W2)^2)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hpoint : ∀ q ∈ circleModuli F r L,
      ‖thetaDualZeroNormalized χ W1 W2 K1 K2 D m3 m4 q‖ ≤ V * (q : ℝ)^(1/4 : ℝ) := by
    intro q hq
    have hLp : 0 < L := lt_of_lt_of_le (by positivity : 0 < 4 * (F * r)) hL
    have hqlow := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    have hqp : 0 < q := by omega
    simpa only [show (1 : ℝ) - 1/8 = 7/8 by norm_num,
      show (2 : ℝ) * (1/8) = 1/4 by norm_num] using
      hnorm χ W1 W2 B1 B2 hB1 hB2 hW1 hW2 K1 K2 hK1 hK2 q D m3 m4 hqp hm3 hm4 hne
  have hb := havg F r L hF hr hFr hL
    (thetaDualZeroNormalized χ W1 W2 K1 K2 D m3 m4) V hV hpoint
  change ‖thetaDualZeroCircleAverage χ W1 W2 K1 K2 D m3 m4 F r L‖ ≤ _ at hb
  convert hb using 1
  dsimp [V]
  ring

end ArtinMatthews
