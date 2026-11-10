module

public import ArtinMatthews.CubicSievePrimeReindex
public import ArtinMatthews.CubicSievePrimeSourceBound
public import ArtinMatthews.MarkedCorrelationEndpoint
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The original centered cubic coefficient has a vanishing prime mean
under the genuine Proposition 5.1 hypothesis. -/

noncomputable section
namespace ArtinMatthews

open Filter Finset OAI OAI.SevenEighths
open scoped BigOperators ContDiff Topology Asymptotics

theorem cubicSieve_actual_prime_correlation_isLittleO
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein, y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₀ : ∀ t, 0 ≤ Φ t) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    (hsource : ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter A hA) Φ x (ε / 1024) Cν) :
    markedPrimeCorrelation Φ 2
      (giantCubicCenteredPrimeCoefficient (cubicNumeratorHeckeCharacter A hA) χ ε)
      =o[atTop] (fun x : ℝ => x / Real.log x) := by
  obtain ⟨C, _, hbound⟩ := cubicSieve_actual_marked_prime_source_bound
  have hΦ₂ : Φ 2 = 0 := by
    by_contra h
    exact (lt_irrefl (2 : ℝ)) (hs h).2
  have hlow (t : ℝ) (ht : t < 1) : Φ t = 0 := by
    by_contra h
    exact (not_lt_of_ge ht.le) (hs h).1
  apply marked_actual_correlation_isLittleO_of_marked Φ (by norm_num : (0 : ℝ) ≤ 2) zero_lt_one
    (hΦ.differentiable (by simp)) (hΦ.continuous_deriv (by simp)) hΦ₂ hΦ₀ hlow
    (giantCubicCenteredPrimeCoefficient (cubicNumeratorHeckeCharacter A hA) χ ε)
    (by norm_num : (0 : ℝ) ≤ 2) (giantCubicCenteredPrimeCoefficient_bound _ χ hε hεq)
    (ε / 64) C 1
  intro n hn
  refine ⟨18601, ?_⟩
  intro e he hinj δ hδ
  have hdepth : 100 * (5 * (30 : ℝ) + 36) < (Fintype.card (Fin 18601) : ℝ) := by norm_num
  filter_upwards [hbound (Fin 18601) e hinj he A hA hnoncube M χ ε hε hεq Φ hΦ hΦ₀ hΦ₁ hs
    hdepth hsource n hn δ hδ,
    literalMarkedArrayMean_lower_eventually e (fun j => (by norm_num : (0 : ℝ) < 1 / 10).trans (he j).1),
    eventually_gt_atTop (1 : ℝ)] with x hx hmean hx₁
  rw [cubicSieve_singleArray_correlation_norm e _ χ ε Φ hs hx₁.le
    ((by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ Fintype.card (Fin 18601)).trans_le hmean)]
  exact hx

end ArtinMatthews
