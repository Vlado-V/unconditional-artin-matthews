module

public import ArtinMatthews.CircleThetaErrorRate
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

/-! For each fixed finite source, the actual smooth Ramanujan approximation
converges to the original shifted theta sum. The preceding quantitative rate
also records the dependence needed when the other parameters vary. -/

noncomputable section
open Filter
open scoped Topology
namespace ArtinMatthews

theorem circleThetaSourceError_tendsto_zero
    (F r : ℕ) (hF : 0 < F) (hr : 0 < r) (hFr : F.Coprime r)
    (χ : OAI.SevenEighths.HeckeFamily.Character) (m1 m2 K1 K2 : ℕ)
    (hm1 : 0 < m1) (hs1 : Squarefree m1)
    (H1 H2 : ℝ → ℂ) (B1 B2 : ℝ) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hw1 : ∀ n ∈ Finset.Icc 1 K1, ‖H1 n‖ ≤ B1)
    (hw2 : ∀ n ∈ Finset.Icc 1 K2, ‖H2 n‖ ≤ B2) :
    Tendsto (fun L : ℕ => circleThetaSourceError χ m1 m2 K1 K2 H1 H2 F r L)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := circleThetaSourceError_bound
  let B : ℝ := C * ((K1 : ℝ) * K2)^2 * B1 * B2 * (F : ℝ) * r *
    (((m2 / (m1.gcd m2)) * K1 + (m1 / (m1.gcd m2)) * K2 : ℕ) : ℝ)^2
  have hlim : Tendsto (fun L : ℕ => B / Real.sqrt L) atTop (𝓝 0) := by
    have h : Tendsto (fun L : ℕ => (L : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
    simpa only [Real.sqrt_eq_rpow] using h.const_div_atTop B
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [eventually_ge_atTop (4 * (F * r))] with L hL
  exact hbound F r L hF hr hFr hL χ m1 m2 K1 K2 hm1 hs1 H1 H2 B1 B2 hB1 hB2 hw1 hw2

end ArtinMatthews
