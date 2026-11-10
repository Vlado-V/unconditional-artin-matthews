module

public import ArtinMatthews.GiantSignedSourceRankCutoff
public import ArtinMatthews.GiantSignedSourceOmissionGain
public import ArtinMatthews.GiantSignedUniformBirthFrame
public import ArtinMatthews.GiantSignedSourceBirthAddressBudget
public import ArtinMatthews.GiantSignedSourceContractionBudget
public import ArtinMatthews.MarkedBirthRankHighSums
public import ArtinMatthews.MarkedBonferroniTail
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! One prime atom per dependent birth pays the literal high-rank
permutation count at the source moment length. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

local instance sourceHighRankPermutationFintype {B : Type*} [Fintype B] {M n H : ℕ} :
    Fintype (Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) :=
  @Equiv.instFintype (GiantSignedUniformBirthAddress B M n H)
    (GiantSignedUniformBirthAddress B M n H) inferInstance inferInstance inferInstance inferInstance

theorem giantSignedSourceBirth_high_rank_sum_eventually
    (C₀ Ch E c scale K₀ : ℝ) (M : ℕ)
    (hC₀ : 0 ≤ C₀) (hCh : 0 ≤ Ch) (hc : 0 < c) (hK₀ : 0 ≤ K₀)
    (hscale : 2*(2*Ch+E+1) ≤ scale) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (B : Type*) [Fintype B],
        let L := Real.log x
        let n := giantTwoSidedSourceMomentLength x
        let R := giantSignedSourceMemoryLimit L
        let r₀ := giantSignedSourceRankCutoff c scale x
        let A := GiantSignedUniformBirthAddress B M n R
        (Fintype.card B : ℝ) ≤ C₀ * Real.log L →
        ∀ F : Equiv.Perm A → ℂ,
          (∀ σ, r₀ ≤ markedBirthPermutationRank σ →
            ‖F σ‖ ≤ (L^Ch)^(n+1) * (K₀/Real.exp (L^c))^(markedBirthPermutationRank σ)) →
          (∑ σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n R),
            if r₀ ≤ markedBirthPermutationRank σ then ‖F σ‖ else 0) ≤ (L^(-E))^n := by
  have ht := ((rpow_mul_exp_neg_rpow_tendsto (30 : ℝ) hc
    (by norm_num : (0 : ℝ) < 1/2)).const_mul K₀).comp Real.tendsto_log_atTop
  simp only [mul_zero] at ht
  filter_upwards [
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    giantSignedSourceBirthAddress_budget_eventually C₀ hC₀ M,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    giantSignedSourceMomentLength_tendsto.eventually (eventually_ge_atTop (30 : ℝ))]
      with x hsmall haddress hlog hn30
  intro B _
  dsimp only
  intro hB F hF
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  let R := giantSignedSourceMemoryLimit L
  let r₀ := giantSignedSourceRankCutoff c scale x
  let A := GiantSignedUniformBirthAddress B M n R
  let D := (Fintype.card A : ℝ)^2+1
  let Δ := K₀ / Real.exp (L^c)
  let W := (L^Ch)^(n+1)
  have hL1 : 1 ≤ L := hlog
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hnR : 1 ≤ (n : ℝ) := (by norm_num : (1 : ℝ) ≤ 30).trans hn30
  have hn : 30 ≤ n := by exact_mod_cast hn30
  have hD1 : 1 ≤ D := by dsimp only [D]; linarith [sq_nonneg (Fintype.card A : ℝ)]
  have hD : D^2 ≤ L^(30 : ℕ) := haddress B hB
  have hΔ : 0 ≤ Δ := div_nonneg hK₀ (Real.exp_nonneg _)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hsmall' : K₀ * L^(30 : ℕ) * Real.exp (-(L^c)/2) ≤ 1 := by
    have he : -(1/2 : ℝ)*L^c = -(L^c)/2 := by ring
    change K₀ * (L^(30 : ℝ) * Real.exp (-(1/2 : ℝ)*L^c)) < 1 at hsmall
    rw [he, Real.rpow_ofNat, ← mul_assoc] at hsmall
    exact hsmall.le
  have hratio : D^2 * Δ ≤ Real.exp (-(L^c)/2) := by
    calc
      _ ≤ L^(30 : ℕ) * Δ := mul_le_mul_of_nonneg_right hD hΔ
      _ = (K₀ * L^(30 : ℕ) * Real.exp (-(L^c)/2)) * Real.exp (-(L^c)/2) := by
        have hexp : Real.exp (-(L^c)) = Real.exp (-(L^c)/2) * Real.exp (-(L^c)/2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [show Δ = K₀ * Real.exp (-(L^c)) by simp only [Δ, div_eq_mul_inv, Real.exp_neg], hexp]
        ring
      _ ≤ _ := mul_le_of_le_one_left (Real.exp_nonneg _) hsmall'
  have hcard₀ : (Fintype.card A : ℝ) ≤ (Fintype.card A : ℝ)^2 := by
    by_cases h : Fintype.card A = 0
    · simp [h]
    · have h' : 1 ≤ (Fintype.card A : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)
      simpa only [one_mul, pow_two] using
        mul_le_mul_of_nonneg_right h' (Nat.cast_nonneg (Fintype.card A) : (0 : ℝ) ≤ _)
  have hcard : ((Fintype.card A+1 : ℕ) : ℝ) ≤ L^n := by
    rw [Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ D := add_le_add hcard₀ le_rfl
      _ ≤ D^2 := by
        simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right hD1 (zero_le_one.trans hD1)
      _ ≤ L^(30 : ℕ) := hD
      _ ≤ _ := pow_le_pow_right₀ hL1 hn
  have hsum := markedBirthRank_high_sum_le (A := A) r₀ (fun σ => ‖F σ‖) hW hΔ hF
  refine hsum.trans ?_
  calc
    _ ≤ ∑ r ∈ Finset.range (Fintype.card A+1), (L^(-(E+1)))^n := by
      apply Finset.sum_le_sum
      intro r _
      split_ifs with hr
      · have hr' : (r₀ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
        have hpay : scale*(n : ℝ)*Real.log L ≤ (r : ℝ)*L^c :=
          (giantSignedSourceRankCutoff_lower (c := c) (scale := scale) hL).trans
            (mul_le_mul_of_nonneg_right hr' (Real.rpow_nonneg hL.le _))
        have hexp : (Real.exp (-(L^c)/2))^r ≤ L^(-scale/2*(n : ℝ)) := by
          rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hL (-scale/2*(n : ℝ))]
          apply Real.exp_le_exp.mpr
          nlinarith only [hpay]
        have he : Ch*((n+1 : ℕ) : ℝ)-scale/2*(n : ℝ) ≤ -(E+1)*(n : ℝ) := by
          push_cast
          nlinarith only [mul_le_mul_of_nonneg_right hnR hCh,
            mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        calc
          D^(2*r)*W*Δ^r = W*(D^2*Δ)^r := by rw [mul_pow,pow_mul]; ring
          _ ≤ W*(Real.exp (-(L^c)/2))^r :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) hΔ) hratio _) hW
          _ ≤ W * L^(-scale/2*(n : ℝ)) := mul_le_mul_of_nonneg_left hexp hW
          _ = L^(Ch*((n+1 : ℕ) : ℝ)-scale/2*(n : ℝ)) := by
            dsimp only [W]
            rw [← Real.rpow_mul_natCast hL.le, ← Real.rpow_add hL]
            congr 1
            ring
          _ ≤ L^(-(E+1)*(n : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL1 he
          _ = _ := Real.rpow_mul_natCast hL.le _ _
      · positivity
    _ = ((Fintype.card A+1 : ℕ) : ℝ) * (L^(-(E+1)))^n := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ L^n * (L^(-(E+1)))^n :=
      mul_le_mul_of_nonneg_right hcard (pow_nonneg (Real.rpow_nonneg hL.le _) _)
    _ = _ := by
      have he : L * L^(-(E+1)) = L^(-E) := by
        calc
          _ = L^(1 : ℝ) * L^(-(E+1)) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hL]; congr 1; ring
      rw [← mul_pow, he]

end
end ArtinMatthews
