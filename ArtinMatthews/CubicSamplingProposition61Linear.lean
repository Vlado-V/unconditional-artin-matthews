module

public import ArtinMatthews.CubicSamplingCentered
public import ArtinMatthews.GiantSamplingShiftedInput
public import ArtinMatthews.CubicSamplingProposition61
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

/-! The literal Section 6.1 class of marking weights consists of fixed
linear combinations of arrays, with the empty array giving constants and
sum-type arrays giving products. -/

noncomputable section
namespace ArtinMatthews

open Filter OAI OAI.SevenEighths
open scoped BigOperators ContDiff Topology

theorem giantCubicSampling_proposition61
    {I : Type*} [Fintype I] {J : I → Type*} [∀ i, Fintype (J i)]
    (e : ∀ i, J i → ℝ) (he : ∀ i j, 0 < e i j ∧ e i j ≤ 1 / 5) (c : I → ℂ)
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
          (fun u => ∑ i, c i * (literalMarkedArrayWeight (e i) x u : ℂ)) Φ ε x r‖) ≤
        x * (Real.log x) ^ (-G) := by
  let η := cubicNumeratorHeckeCharacter A hA
  let C := ∑ i, ‖c i‖
  have hs' := eventually_all.mpr fun i =>
    giantCubicSampling_literalArray_centered_log_saving (e i) (he i)
      A hA hnoncube χ hε hεq Φ hΦ hΦ₁ hs hsource (G + 1)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop C)
  filter_upwards [hs', hlog, eventually_gt_atTop (1 : ℝ)] with x hx hL hx₁
  let H (i : I) (u : ℕ) : ℂ := (literalMarkedArrayWeight (e i) x u : ℂ)
  let F (i : I) (r : ℕ) := giantCubicSamplingCenteredSum η χ (H i) Φ ε x r
  let R := ⌊x ^ (ε / 64)⌋₊
  have hsplit (r : ℕ) :
      giantCubicSamplingCenteredSum η χ (fun u => ∑ i, c i * H i u) Φ ε x r =
        ∑ i, c i * F i r := by
    dsimp only [F]
    unfold giantCubicSamplingCenteredSum
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _hu
    ring
  have hLogPos := Real.log_pos hx₁
  have hpower : (Real.log x) ^ (-(G + 1)) * Real.log x = (Real.log x) ^ (-G) := by
    calc
      _ = (Real.log x) ^ (-(G + 1)) * (Real.log x) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (Real.log x) ^ (-(G + 1) + 1) := (Real.rpow_add hLogPos _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 R, ∑ i, ‖c i‖ * ‖F i r‖ := by
      apply Finset.sum_le_sum
      intro r _hr
      change ‖giantCubicSamplingCenteredSum η χ (fun u => ∑ i, c i * H i u) Φ ε x r‖ ≤ _
      rw [hsplit]
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun i => c i * F i r)
    _ = ∑ i, ‖c i‖ * ∑ r ∈ Finset.Icc 1 R, ‖F i r‖ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ i, ‖c i‖ * (x * (Real.log x) ^ (-(G + 1))) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i) (norm_nonneg _))
    _ = C * (x * (Real.log x) ^ (-(G + 1))) := (Finset.sum_mul _ _ _).symm
    _ ≤ Real.log x * (x * (Real.log x) ^ (-(G + 1))) :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    _ = _ := by
      calc
        _ = x * ((Real.log x) ^ (-(G + 1)) * Real.log x) := by ring
        _ = _ := by rw [hpower]

end ArtinMatthews
