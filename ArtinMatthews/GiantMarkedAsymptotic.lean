module

public import ArtinMatthews.GiantMarkedEnvelope
public import ArtinMatthews.MarkedArrayAsymptotic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! All-logarithmic giant-window progression saving from explicit structural
prime bounds, with no progression distribution premise. -/

namespace ArtinMatthews

open Filter MeasureTheory
open scoped BigOperators Asymptotics Topology

structure GiantWindowAsymptoticBounds {ι : Type*} [Fintype ι]
    (G : Finset ℕ) (P : ι → Finset ℕ) (α gexp x : ℝ) : Prop where
  prime : ∀ ell ∈ G, ell.Prime
  disjoint : Disjoint G (Finset.univ.biUnion P)
  lower : ∀ ell ∈ G, Real.exp ((Real.log x) ^ α) ≤ (ell : ℝ)
  cardinality : (G.card : ℝ) ≤ x ^ gexp
  reciprocal : (∑ ell ∈ G, 1 / (ell : ℝ)) ≤ 1

theorem giant_marked_array_progression_all_log_tendsto {ι : Type*} [Fintype ι]
    (G : ℝ → Finset ℕ) (P : ℝ → ι → Finset ℕ) (W : ℝ → ι → ℝ)
    (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (α β δ c gexp v V C A : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ) (hsum : δ + β < 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hlevel : c + gexp < 1)
    (hv : 0 < v) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hband : ∀ᶠ x : ℝ in atTop, MarkedArrayAsymptoticBounds (P x) (W x) a α β v V C x)
    (hgiant : ∀ᶠ x : ℝ in atTop, GiantWindowAsymptoticBounds (G x) (P x) α gexp x)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A / x *
      giantMarkedArrayProgressionDiscrepancy (G x) (P x) (W x) a Φ T x ⌊x ^ c⌋₊)
      atTop (𝓝 0) := by
  let B := ((3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) / v ^ (∑ i, a i) +
    (∫ t in Set.Ioc 0 T, Φ t) * C)
  have hlimit := (markedProgressionEnvelope_tendsto α β δ (c + gexp) (((∑ i, a i : ℕ) : ℝ) + 1) V A
    (∑ i, a i) hα hβ hδ hsum hlevel hV).const_mul B
  simp only [mul_zero] at hlimit
  apply squeeze_zero' _ _ hlimit
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (div_nonneg (Real.rpow_nonneg (Real.log_pos hx).le _) (by linarith))
      (giantMarkedArrayProgressionDiscrepancy_nonneg _ _ _ _ _ _ _ _)
  · filter_upwards [hband, hgiant, eventually_gt_atTop (1 : ℝ)] with x hb hg hx
    have hbound := giant_marked_array_progression_envelope_bound (G x) (P x) (W x) a ha
      hb.disjoint hb.prime α β δ c v V C x gexp hx hc0 hc1 hv hV hC hb.lower hb.upper
      hb.normalizer hb.primeMass hb.coefficientMass hg.prime hg.disjoint hg.lower
      hg.cardinality hg.reciprocal Φ hT hΦ hderiv hΦT hΦ0
    have h := mul_le_mul_of_nonneg_left hbound
      (div_nonneg (Real.rpow_nonneg (Real.log_pos hx).le A) (show 0 ≤ x by linarith))
    convert h using 1
    ring

theorem giant_marked_array_progression_all_log_isLittleO {ι : Type*} [Fintype ι]
    (G : ℝ → Finset ℕ) (P : ℝ → ι → Finset ℕ) (W : ℝ → ι → ℝ)
    (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (α β δ c gexp v V C A : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ) (hsum : δ + β < 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hlevel : c + gexp < 1)
    (hv : 0 < v) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hband : ∀ᶠ x : ℝ in atTop, MarkedArrayAsymptoticBounds (P x) (W x) a α β v V C x)
    (hgiant : ∀ᶠ x : ℝ in atTop, GiantWindowAsymptoticBounds (G x) (P x) α gexp x)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (fun x : ℝ => giantMarkedArrayProgressionDiscrepancy (G x) (P x) (W x) a Φ T x ⌊x ^ c⌋₊)
      =o[atTop] (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact fun h => (mul_pos (by linarith : 0 < x)
      (Real.rpow_pos_of_pos (Real.log_pos hx) (-A))).ne' h |>.elim
  · apply (giant_marked_array_progression_all_log_tendsto G P W a ha α β δ c gexp v V C A
      hα hβ hδ hsum hc0 hc1 hlevel hv hV hC hband hgiant Φ hT hΦ hderiv hΦT hΦ0).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [Real.rpow_neg (Real.log_pos hx).le]
    field_simp

end ArtinMatthews
