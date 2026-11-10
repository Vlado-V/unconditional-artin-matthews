module

public import ArtinMatthews.GiantMarkedCharacterCriterion
public import ArtinMatthews.GiantMarkedSelectedDamping
public import ArtinMatthews.GiantMarkedSelectedSquareActual
public import ArtinMatthews.MarkedMajorTypeIICoefficients
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

/-! The actual prime-minus-rough coefficient and the fixed-character
giant-prime test satisfy the square-divisibility replacement hypotheses. -/

noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

theorem giant_marked_centered_quotient_damping_log_saving {J : Type*}
    [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j, (1 / 10 : ℝ) < e j ∧ e j < (1 / 5 : ℝ))
    (δ C A : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop,
      let P := fun j => markedLogPowerBand (e j) (Real.exp L)
      let W := Real.exp (L ^ (6 / 25 : ℝ))
      ∀ (Hm Hn modulation : ℝ) (M N : Finset ℕ) (β F : ℕ → ℂ),
        Real.exp (δ * L) ≤ Hm → Real.exp (δ * L) ≤ Hn →
        (∀ m ∈ M, Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm) →
        (∀ n ∈ N, Hn ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Hn) →
        (∀ n ∈ N, ‖β n‖ ≤ L ^ C) →
        (∀ u, ‖F u‖ ≤ 1) → (∀ j p, p ∈ P j → ∀ h, F (p * h) = F h) →
        ‖(∑ m ∈ M, ∑ n ∈ N, markedMajorCenteredCoefficient W modulation m * β n *
          F (m * n - 1) * (literalMarkedArrayWeight e (Real.exp L) (m * n - 1) : ℂ)) -
          giantMarkedQuotientDampedSum P M N (markedMajorCenteredCoefficient W modulation) β F‖ ≤
          Hm * Hn * L ^ (-A) := by
  filter_upwards [giant_marked_quotient_damping_log_saving e hinj he δ 2 C A hδ,
    markedMajorTypeII_alpha_bound δ hδ] with L herror hα
  dsimp only
  intro Hm Hn modulation M N β F hHm hHn hM hN hβ hFnorm hF
  refine herror Hm Hn M N _ β F hHm hHn hM hN ?_ hβ hFnorm hF
  intro m hm
  simpa only [Real.rpow_two] using hα m modulation (hHm.trans (hM m hm).1)

theorem giant_marked_character_giant_quotient_damping_log_saving {J : Type*}
    [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j, (1 / 10 : ℝ) < e j ∧ e j < (1 / 5 : ℝ))
    (δ C A : ℝ) (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4) :
    ∀ᶠ L : ℝ in atTop,
      let P := fun j => markedLogPowerBand (e j) (Real.exp L)
      let W := Real.exp (L ^ (6 / 25 : ℝ))
      let F := giantMarkedCenteredCore ε (Real.exp L)
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q)
        (Hm Hn modulation : ℝ) (M N : Finset ℕ) (β : ℕ → ℂ),
        Real.exp (δ * L) ≤ Hm → Real.exp (δ * L) ≤ Hn →
        (∀ m ∈ M, Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm) →
        (∀ n ∈ N, Hn ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Hn) →
        (∀ n ∈ N, ‖β n‖ ≤ L ^ C) →
        ‖(∑ m ∈ M, ∑ n ∈ N, χ (m * n) * markedMajorCenteredCoefficient W modulation m *
          β n * F (m * n - 1) * (literalMarkedArrayWeight e (Real.exp L) (m * n - 1) : ℂ)) -
          giantMarkedQuotientDampedSum P M N (giantFixedCharacterReplacementCoefficient χ W modulation)
            (fun n => χ n * β n) F‖ ≤ Hm * Hn * L ^ (-A) := by
  have hcore := Real.tendsto_exp_atTop.eventually
    (giantMarkedCenteredCore_interface e (fun j => (he j).2.trans (by norm_num)) hε hεq)
  filter_upwards [giant_marked_quotient_damping_log_saving e hinj he δ 2 C A hδ,
    markedMajorTypeII_alpha_bound δ hδ, hcore] with L herror hα hF
  let W := Real.exp (L ^ (6 / 25 : ℝ))
  let F := giantMarkedCenteredCore ε (Real.exp L)
  dsimp only
  intro q χ Hm Hn modulation M N β hHm hHn hM hN hβ
  let a := giantFixedCharacterReplacementCoefficient χ W modulation
  let b := fun n : ℕ => χ n * β n
  have ha (m : ℕ) (hm : m ∈ M) : ‖a m‖ ≤ L ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    exact (giantFixedCharacterReplacementCoefficient_norm_le χ W modulation m).trans
      (hα m modulation (hHm.trans (hM m hm).1))
  have hb (n : ℕ) (hn : n ∈ N) : ‖b n‖ ≤ L ^ C := by
    change ‖χ n * β n‖ ≤ _
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans (hβ n hn)
  have hsplit :
      (∑ m ∈ M, ∑ n ∈ N, χ (m * n) * markedMajorCenteredCoefficient W modulation m *
        β n * F (m * n - 1) * (literalMarkedArrayWeight e (Real.exp L) (m * n - 1) : ℂ)) =
        ∑ m ∈ M, ∑ n ∈ N, a m * b n * F (m * n - 1) *
          (literalMarkedArrayWeight e (Real.exp L) (m * n - 1) : ℂ) := by
    apply Finset.sum_congr rfl
    intro m _hm
    apply Finset.sum_congr rfl
    intro n _hn
    simp only [map_mul, a, b, giantFixedCharacterReplacementCoefficient]
    ring
  rw [hsplit]
  exact herror Hm Hn M N a b F hHm hHn hM hN ha hb hF.1 hF.2

end ArtinMatthews
