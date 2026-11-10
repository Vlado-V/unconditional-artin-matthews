module

public import ArtinMatthews.GiantTwoSidedRootMargin
public import ArtinMatthews.GiantTwoSidedRawPositionCutoff
public import ArtinMatthews.GiantRawPositionGeometry
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

namespace ArtinMatthews
open Filter Finset
open scoped Topology
noncomputable section

theorem giantPhysicalDyadic_scale_le {N j : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hN : (N : ℝ) ≤ x ^ 2) (hj : j ∈ range (Nat.log 2 N + 1)) :
    ((2 ^ j : ℕ) : ℝ) ≤ x ^ 2 := by
  have hj' := mem_range.mp hj
  by_cases hzero : N = 0
  · subst N
    rw [Nat.log_zero_right] at hj'
    have hj0 : j = 0 := by omega
    subst j
    simpa only [pow_zero, Nat.cast_one] using
      (show (1 : ℝ) ≤ x ^ 2 by nlinarith only [hx, sq_nonneg (x - 1)])
  · have hlog : j ≤ Nat.log 2 N := Nat.lt_succ_iff.mp hj'
    have hpow : (2 : ℕ) ^ j ≤ N :=
      (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hlog).trans (Nat.pow_log_le_self 2 hzero)
    exact (Nat.cast_le.mpr hpow).trans hN

theorem giantPhysicalDyadic_lowerCutoff_eventually {a τ : ℝ} (ha : 0 < a) (hτ1 : τ < 1) :
    ∀ᶠ x : ℝ in atTop, 2 * x ^ τ ≤ a * x := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr hτ1)).eventually_ge_atTop (2 / a)] with x hx hpow
  have hscale : (2 / a) * x ^ τ ≤ x := by
    calc
      _ ≤ x ^ (1 - τ) * x ^ τ := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hx.le _)
      _ = x := by
        rw [← Real.rpow_add hx, show 1 - τ + τ = 1 by ring, Real.rpow_one]
  rw [div_mul_eq_mul_div₀] at hscale
  simpa only [mul_comm x a] using (div_le_iff₀ ha).mp hscale

theorem giantPhysicalDyadic_scale_ge_of_support {x a τ : ℝ} (hx : 0 < x)
    (ha : 0 < a) (hscale : 2 * x ^ τ ≤ a * x) {j n D : ℕ}
    (hn : n ∈ giantTwoSidedRootInterval ((2 ^ j : ℕ) : ℝ)) (hD : 0 < D)
    {Ψ : ℝ → ℂ} (hΨ : Function.support Ψ ⊆ Set.Ici a)
    (hcut : Ψ ((n : ℝ) / (x * (D : ℝ))) ≠ 0) :
    x ^ τ ≤ ((2 ^ j : ℕ) : ℝ) := by
  have hden : 0 < x * (D : ℝ) := mul_pos hx (Nat.cast_pos.mpr hD)
  have hlo : a ≤ (n : ℝ) / (x * (D : ℝ)) := hΨ hcut
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hmain : a * x ≤ (n : ℝ) := by
    calc
      a * x = a * (x * 1) := by rw [mul_one]
      _ ≤ a * (x * (D : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD1 hx.le) ha.le
      _ ≤ (n : ℝ) := (le_div_iff₀ hden).mp hlo
  have hupper := (giantTwoSidedRootInterval_bounds hn).2
  linarith only [hscale, hmain, hupper]

theorem giantCandidateRawDyadic_geometry_eventually (k : ℕ) {T a τ : ℝ}
    (hT : 0 < T) (ha : 0 < a) (hτ1 : τ < 1) :
    ∀ᶠ x : ℝ in atTop, ∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let U := ⌊T * x⌋₊
      let N := giantTwoSidedSharedProductMax P k * (U + 1)
      (N : ℝ) ≤ x ^ 2 ∧
        giantTwoSidedRawPositionBox P k U ∪ giantTwoSidedRawPositionBox P k (U + 1) = Ioc 0 N ∧
        giantTwoSidedRawPositionBox P k U ∪ giantTwoSidedRawPositionBox P k (U + 1) ⊆ Ioc 0 ⌊x ^ 2⌋₊ ∧
        ∀ j ∈ range (Nat.log 2 N + 1), ((2 ^ j : ℕ) : ℝ) ≤ x ^ 2 ∧
          ∀ {n D : ℕ}, n ∈ giantTwoSidedRootInterval ((2 ^ j : ℕ) : ℝ) → 0 < D →
            ∀ {Ψ : ℝ → ℂ}, Function.support Ψ ⊆ Set.Ici a →
              Ψ ((n : ℝ) / (x * (D : ℝ))) ≠ 0 → x ^ τ ≤ ((2 ^ j : ℕ) : ℝ) := by
  filter_upwards [giantCandidateRawPositionBox_cap_eventually k hT,
    giantPhysicalDyadic_lowerCutoff_eventually ha hτ1, eventually_ge_atTop (1 : ℝ)]
    with x hcap hlo hx
  intro S
  obtain ⟨hN, hbox⟩ := hcap S
  refine ⟨hN, giantTwoSidedRawPositionBox_union_succ _ _ _, hbox, ?_⟩
  intro j hj
  refine ⟨giantPhysicalDyadic_scale_le hx hN hj, ?_⟩
  exact giantPhysicalDyadic_scale_ge_of_support (zero_lt_one.trans_le hx) ha hlo

end
end ArtinMatthews
