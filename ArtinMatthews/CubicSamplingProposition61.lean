module

public import ArtinMatthews.CubicSamplingCentered
public import ArtinMatthews.GiantSamplingShiftedInput
public import ArtinMatthews.CubicSamplingArrayGroups
public import ArtinMatthews.CubicSamplingBaselineJoin
public import ArtinMatthews.GiantSamplingActualArrays
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

/-! Proposition 6.1 for a literal marking array. The only analytic input is
the exact shifted bilinear coefficient estimate of Proposition 5.1. -/

noncomputable section
namespace ArtinMatthews

open Filter OAI OAI.SevenEighths
open scoped BigOperators ContDiff Topology

theorem giantCubicSampling_literalArray_baseline_log_saving {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {ε : ℝ} (hε : ε < 1 / 4)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2) (G : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      (∑ r ∈ Finset.Icc 1 ⌊x ^ (ε / 64)⌋₊,
        ‖giantCubicSamplingBaselineSum (cubicNumeratorHeckeCharacter A hA) χ
          (fun u => (literalMarkedArrayWeight e x u : ℂ)) Φ x r‖) ≤
        x * (Real.log x) ^ (-G) := by
  let J' := ↥(cubicSamplingBandLabels e)
  let e' (s : J') : ℝ := s.val
  let a (s : J') : ℕ := cubicSamplingBandMultiplicity e s
  have he' (s : J') : 0 < e' s ∧ e' s ≤ 1 / 5 := by
    obtain ⟨j, _hj, hj⟩ := Finset.mem_image.mp s.2
    change 0 < (s : ℝ) ∧ (s : ℝ) ≤ 1 / 5
    rw [← hj]
    exact he j
  have hh := giantCubicSampling_actualArray_baseline_log_saving e' he' Subtype.val_injective a
    (cubicSampling_bandMultiplicity_pos e) A hA hnoncube χ hε Φ hΦ hΦ₁ hs G
  filter_upwards [hh] with x hx
  have hH : (fun u => (literalMarkedArrayWeight e x u : ℂ)) =
      fun u => ((∏ s : J', (bandWeight (markedLogPowerBand (e' s) x)
        (bandReciprocalMass (markedLogPowerBand (e' s) x)) u) ^ a s : ℝ) : ℂ) := by
    funext u
    exact congrArg (fun z : ℝ => (z : ℂ)) (cubicSampling_literalArray_eq_grouped e x u)
  rw [hH]
  exact hx

theorem giantCubicSampling_literalArray_centered_log_saving {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    (hsource : ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter A hA) Φ x (ε / 1024) Cν)
    (G : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      (∑ r ∈ Finset.Icc 1 ⌊x ^ (ε / 64)⌋₊,
        ‖giantCubicSamplingCenteredSum (cubicNumeratorHeckeCharacter A hA) χ
          (fun u => (literalMarkedArrayWeight e x u : ℂ)) Φ ε x r‖) ≤
        x * (Real.log x) ^ (-G) := by
  let η := cubicNumeratorHeckeCharacter A hA
  let H (x : ℝ) (u : ℕ) : ℂ := (literalMarkedArrayWeight e x u : ℂ)
  have hg : ∀ᶠ x : ℝ in atTop,
      (∑ r ∈ Finset.Icc 1 ⌊x ^ (ε / 64)⌋₊,
        ‖giantCubicSamplingGiantSum η χ (H x) Φ ε x r‖) ≤ x * (Real.log x) ^ (-(G + 1)) := by
    have hh := giantCubicSampling_actual_arrays_log_saving (I := Unit) (J := fun _ => J)
      (fun _ => e) (fun _ j => ⟨(he j).1, (he j).2.trans_lt (by norm_num)⟩)
      (fun _ => 1) η χ hε hεq Φ hΦ₁ hs hsource (G + 1)
    filter_upwards [hh] with x hx
    simpa only [Fintype.sum_unique, one_mul, H] using hx
  have hb := giantCubicSampling_literalArray_baseline_log_saving e he A hA hnoncube χ hεq
    Φ hΦ hΦ₁ hs (G + 1)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hg, hb, hlog, giantPrimeReciprocalSum_bounds_eventually hε hεq,
    eventually_ge_atTop (4 : ℝ)] with x hxG hxB hxLog hxC hx
  let R := ⌊x ^ (ε / 64)⌋₊
  have hCx : ‖(giantPrimeReciprocalSum x ε : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_of_nonneg hxC.1] using hxC.2
  have hrow (r : ℕ) :
      ‖giantCubicSamplingCenteredSum η χ (H x) Φ ε x r‖ ≤
        ‖giantCubicSamplingGiantSum η χ (H x) Φ ε x r‖ +
          ‖giantCubicSamplingBaselineSum η χ (H x) Φ x r‖ := by
    rw [giantCubicSamplingCenteredSum_eq η χ (H x) Φ hx hεq.le r]
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    exact add_le_add le_rfl (mul_le_of_le_one_left (norm_nonneg _) hCx)
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 R, (‖giantCubicSamplingGiantSum η χ (H x) Φ ε x r‖ +
        ‖giantCubicSamplingBaselineSum η χ (H x) Φ x r‖) :=
      Finset.sum_le_sum (fun r _ => hrow r)
    _ = (∑ r ∈ Finset.Icc 1 R, ‖giantCubicSamplingGiantSum η χ (H x) Φ ε x r‖) +
        ∑ r ∈ Finset.Icc 1 R, ‖giantCubicSamplingBaselineSum η χ (H x) Φ x r‖ :=
      Finset.sum_add_distrib
    _ ≤ x * (Real.log x) ^ (-(G + 1)) + x * (Real.log x) ^ (-(G + 1)) := add_le_add hxG hxB
    _ ≤ _ := cubicSampling_two_log_errors (by linarith) hxLog G

end ArtinMatthews
