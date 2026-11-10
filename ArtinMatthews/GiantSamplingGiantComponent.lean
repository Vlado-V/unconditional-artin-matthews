module

public import ArtinMatthews.GiantSamplingDyads
public import ArtinMatthews.GiantSamplingShiftedInput
public import ArtinMatthews.GiantSamplingCofactorBox
public import ArtinMatthews.GiantSamplingSourceBudget
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The full giant-factor component of Proposition 6.1 has the source
power saving once the literal Proposition 5.1 estimate is supplied. -/

noncomputable section
namespace ArtinMatthews

open Filter
open OAI OAI.SevenEighths
open scoped BigOperators Topology

theorem giantCubicSampling_giantComponent_power_saving (η : HeckeFamily.Character)
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {ε : ℝ}
    (hε : 0 < ε) (hεq : ε < 1 / 4)
    (Φ : ℝ → ℝ) (hΦ : ∀ t, ‖Φ t‖ ≤ 1) (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    (hsource : ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
      GiantSamplingShiftedBilinearBound η Φ x (ε / 1024) Cν) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (H : ℕ → ℂ) (C : ℝ), 0 < C →
        (∀ k ∈ giantSamplingActiveCofactors x ε, ‖H k‖ ≤ C) →
        (∀ ℓ ∈ giantPrimeWindow x ε, ∀ k, H (ℓ * k) = H k) →
        (∑ r ∈ Finset.Icc 1 ⌊x ^ (ε / 64)⌋₊, ‖giantCubicSamplingGiantSum η χ H Φ ε x r‖) ≤
          C₀ * C * x ^ (1 - ε / 128) := by
  obtain ⟨Cν, hCν, hsource⟩ := hsource
  let ν := ε / 1024
  obtain ⟨Ctail, hCtail, hbox⟩ := giantCubicSampling_cofactorBox_norm_le η χ ν
    (div_pos hε (by norm_num))
  let Kpow := (2 : ℝ) ^ (1 / 2 : ℝ) + 4 * (4 : ℝ) ^ (3 / 8 : ℝ)
  let Cbox := (M : ℝ) ^ 2 * Cν * Kpow + Ctail
  let Cdyad := 2 + 128 / Real.log 2
  have hCbox : 0 < Cbox := add_pos_of_nonneg_of_pos (by positivity) hCtail
  have hCdyad : 0 < Cdyad := by dsimp only [Cdyad]; positivity
  refine ⟨Cdyad * Cbox, mul_pos hCdyad hCbox, ?_⟩
  filter_upwards [hsource, giantSampling_source_cutoffs_eventually hε] with x hx hcut
  obtain ⟨hx₁, hD, hDT⟩ := hcut
  have hx₀ := zero_lt_one.trans_le hx₁
  intro H C hC hH hinv
  let R := ⌊x ^ (ε / 64)⌋₊
  let D := x ^ (ε / 32)
  let K := giantSamplingActiveCofactors x ε
  let I := giantSamplingDyadIndices K
  let Krow := giantSamplingDyadCofactors K
  let T (i : ℕ) := ((2 ^ i : ℕ) : ℝ)
  let E := x ^ (1 - ε / 64)
  have hE : 0 ≤ E := Real.rpow_nonneg hx₀.le _
  have hper (i : ℕ) (hi : i ∈ I) :
      (∑ r ∈ Finset.Icc 1 R, ‖giantCubicSamplingCofactorSum η χ H Φ ε x r (Krow i)‖) ≤
        C * Cbox * E := by
    obtain ⟨hlo, hhi, hK⟩ := giantSampling_active_dyad_bounds hx₀.le hi
    have hT : 0 < T i := Nat.cast_pos.mpr (pow_pos (by decide : 0 < (2 : ℕ)) i)
    have hnorm (k : ℕ) (hk : k ∈ Krow i) : ‖H k‖ ≤ C :=
      hH k (Finset.mem_filter.mp hk).1
    let P := (R : ℝ) ^ 2 * x ^ ν *
      (x * T i ^ (-(1 / 2) : ℝ) * D ^ 2 +
        x ^ (7 / 8 : ℝ) * (2 * T i) ^ (3 / 8 : ℝ) * (4 * D ^ (1 / 4 : ℝ)))
    let Q := x ^ (1 + 2 * ν) / D
    have hsmall : P ≤ Kpow * E := giantSampling_source_smallBudget_le hx₁ hε hεq hlo hhi
    have hlarge : Q ≤ E := giantSampling_source_largeBudget_le hx₁ hε
    calc
      _ ≤ (R : ℝ) ^ 2 * (M : ℝ) ^ 2 * C * (Cν * x ^ ν) *
          (x * T i ^ (-(1 / 2) : ℝ) * D ^ 2 +
            x ^ (7 / 8 : ℝ) * (2 * T i) ^ (3 / 8 : ℝ) * (4 * D ^ (1 / 4 : ℝ))) +
          Ctail * C * x ^ (1 + 2 * ν) / D :=
        hbox H Φ ε x (T i) D C Cν R (Krow i) hx₁ hT hD (hDT.trans hlo)
          hC hCν.le hK hnorm hΦ hs hx
      _ = (M : ℝ) ^ 2 * C * Cν * P + Ctail * C * Q := by
        dsimp only [P, Q]
        ring
      _ ≤ (M : ℝ) ^ 2 * C * Cν * (Kpow * E) + Ctail * C * E :=
        add_le_add (mul_le_mul_of_nonneg_left hsmall (by positivity))
          (mul_le_mul_of_nonneg_left hlarge (by positivity))
      _ = _ := by dsimp only [Cbox]; ring
  have hsum (r : ℕ) : giantCubicSamplingGiantSum η χ H Φ ε x r =
      ∑ i ∈ I, giantCubicSamplingCofactorSum η χ H Φ ε x r (Krow i) :=
    (giantCubicSamplingGiantSum_eq_activeCofactors η χ H Φ r hx₀ hs hinv).trans
      (giantCubicSamplingCofactorSum_eq_dyads η χ H Φ ε x r K)
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 R, ∑ i ∈ I,
        ‖giantCubicSamplingCofactorSum η χ H Φ ε x r (Krow i)‖ := by
      apply Finset.sum_le_sum
      intro r _hr
      rw [hsum]
      exact norm_sum_le _ _
    _ = ∑ i ∈ I, ∑ r ∈ Finset.Icc 1 R,
        ‖giantCubicSamplingCofactorSum η χ H Φ ε x r (Krow i)‖ := Finset.sum_comm
    _ ≤ ∑ _i ∈ I, C * Cbox * E := Finset.sum_le_sum hper
    _ = (I.card : ℝ) * (C * Cbox * E) := by simp
    _ ≤ (Cdyad * x ^ (ε / 128)) * (C * Cbox * E) :=
      mul_le_mul_of_nonneg_right (giantSampling_active_dyad_card_subpower hx₁ hε)
        (mul_nonneg (mul_nonneg hC.le hCbox.le) hE)
    _ = _ := by
      rw [show 1 - ε / 128 = ε / 128 + (1 - ε / 64) by ring, Real.rpow_add hx₀]
      dsimp only [E]
      ring

end ArtinMatthews
