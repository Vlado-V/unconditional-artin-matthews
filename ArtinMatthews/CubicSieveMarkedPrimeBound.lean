module

public import ArtinMatthews.CubicSieveRoughCorollary
public import ArtinMatthews.CubicSievePrimeExtraction
public import Mathlib.Order.CompletePartialOrder
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

/-! The actual marked prime test inherits Corollary 7.2 once the literal
cubic Mellin boxes are bounded. The fixed array normalization does not
change the source sieve constant. -/

noncomputable section
namespace ArtinMatthews

open Filter OAI OAI.SevenEighths
open scoped Asymptotics ContDiff

theorem cubicSieve_actual_marked_prime_bound {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₀ : ∀ t, 0 ≤ Φ t) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    (hsource : ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter A hA) Φ x (ε / 1024) Cν)
    (m : ℕ) (C : ℝ) (herror : CubicSieveDivisorWeightedBound e Φ ε m C)
    (hboxes : CubicSieveExtractionBoxSaving e (cubicNumeratorHeckeCharacter A hA) χ Φ hΦ
      (hs.trans (fun _ ht => ⟨ht.1.le, ht.2.le.trans (by norm_num)⟩))
      ε (cubicSieveSourceExponent ε m))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,
      cubicSieveNormalizedScale e x *
        ‖markedActualPrimeThetaSum e (cubicNumeratorHeckeCharacter A hA) χ
          (giantMarkedCenteredCore ε) Φ 3 x‖ ≤
        C * Real.exp (-(2 * (m : ℝ))) / (cubicSieveSourceExponent ε m) ^ 2 + δ := by
  let γ := cubicSieveSourceExponent ε m
  let η := cubicNumeratorHeckeCharacter A hA
  let K := (1 / 2 : ℝ) ^ Fintype.card J
  let d := δ / 2
  have hK : 0 < K := by dsimp only [K]; positivity
  have hd : 0 < d := half_pos hδ
  obtain ⟨hγ, hγ₁, _hlevel⟩ := cubicSieve_sourceExponent_bounds hε hεq m
  have hSupp : Function.support Φ ⊆ Set.Icc 1 3 :=
    hs.trans (fun _ ht => ⟨ht.1.le, ht.2.le.trans (by norm_num)⟩)
  have hdif := (cubicSieve_rough_sub_prime_isLittleO e he η χ hε hεq hγ
    (hγ₁.trans (by norm_num)) Φ hΦ hSupp hboxes).bound (mul_pos hK hd)
  have hr := cubicSieve_actual_rough_bound e he A hA hnoncube χ hε hεq Φ hΦ hΦ₀ hΦ₁
    hs hsource m C herror d hd
  have hm := literalMarkedArrayMean_lower_eventually e (fun j => (he j).1)
  filter_upwards [hdif, hr, hm, eventually_gt_atTop (1 : ℝ)] with x hxDif hxR hxMean hx₁
  let W := literalMarkedArrayMean e x
  let L := Real.log x
  let S := cubicSieveNormalizedScale e x
  let R := markedActualRoughThetaSum e η χ (giantMarkedCenteredCore ε) Φ 3 γ x
  let P := markedActualPrimeThetaSum e η χ (giantMarkedCenteredCore ε) Φ 3 x
  have hx₀ := zero_lt_one.trans hx₁
  have hL : 0 < L := Real.log_pos hx₁
  have hW : 0 < W := hK.trans_le hxMean
  have hS : 0 ≤ S := div_nonneg hL.le (mul_pos hx₀ hW).le
  have hDiff : S * ‖R - P‖ ≤ d := by
    have hnorm : ‖x * L ^ (-1 : ℝ)‖ = x / L := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv, Real.norm_of_nonneg (div_nonneg hx₀.le hL.le)]
    calc
      _ ≤ S * ((K * d) * ‖x * L ^ (-1 : ℝ)‖) := mul_le_mul_of_nonneg_left hxDif hS
      _ = d * (K / W) := by
        rw [hnorm]
        change L / (x * W) * ((K * d) * (x / L)) = _
        field_simp [hx₀.ne', hW.ne', hL.ne']
      _ ≤ _ := mul_le_of_le_one_right hd.le ((div_le_one hW).mpr hxMean)
  have hP : ‖P‖ ≤ ‖R‖ + ‖R - P‖ := by
    calc
      _ = ‖R - (R - P)‖ := congrArg norm (sub_sub_cancel R P).symm
      _ ≤ _ := norm_sub_le _ _
  calc
    _ ≤ S * (‖R‖ + ‖R - P‖) := mul_le_mul_of_nonneg_left hP hS
    _ = S * ‖R‖ + S * ‖R - P‖ := mul_add _ _ _
    _ ≤ (C * Real.exp (-(2 * (m : ℝ))) / γ ^ 2 + d) + d := add_le_add hxR hDiff
    _ = _ := by dsimp only [d, γ]; ring

end ArtinMatthews
