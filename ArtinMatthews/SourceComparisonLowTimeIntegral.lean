module

public import ArtinMatthews.GiantCandidateGroups
public import ArtinMatthews.SourceComparisonActualLowTime
public import ArtinMatthews.SourceComparisonLowTimeEventual
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The checked pointwise saving gives the literal low-Mellin part
of the ordinary comparison estimate. -/
namespace ArtinMatthews
open Filter Finset MeasureTheory
open scoped BigOperators
noncomputable section

universe u v
variable {J : Type u} [Fintype J] {G : Type v} [Fintype G]

theorem sourceComparisonCenteredMellinSum_continuous (e : J → ℝ) (ε x Y σ B : ℝ)
    (ψ : ℝ → ℂ) (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (k : ℕ) [NeZero k] (h : ℤ) :
    Continuous (sourceComparisonCenteredMellinSum e ε x Y σ B ψ P t q b k h) := by
  unfold sourceComparisonCenteredMellinSum
  apply Continuous.div_const
  apply continuous_finsetSum
  intro n hn
  have hn₀ : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (mem_Ioc.mp hn).1.ne'
  simp_rw [Complex.cpow_def_of_ne_zero hn₀]
  exact continuous_const.mul (Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.mul continuous_const)))

theorem sourceComparisonCenteredMellinSum_lowTime_integral_eventually (e : J → ℝ)
    (he : ∀ j, (1/10 : ℝ) < e j ∧ e j < 1/5) (heinj : Function.Injective e)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {a b₀ B : ℝ} (ha : 0 < a) (hab : a ≤ b₀) (hB : b₀ < B) (C S F A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ {G : Type v} [Fintype G] (i : G ↪ GiantCandidateGroupIndex x)
      (t : G → ℕ), (∀ g, t g ≤ m) →
      ∀ (q : G → ℝ), (∀ g, 0 ≤ q g ∧ q g ≤ 1) →
      ∀ (b : ((g : G) → Fin (t g) → ℕ) → ℂ),
        (∀ l ∈ sourceComparisonMarkChoices (giantCandidateGroup x ∘ i) t, ‖b l‖ ≤ 1) →
      ∀ (Y σ : ℝ), x ^ (1 - ε/4) ≤ Y → Y ≤ x ^ (1 + ε/4) → |σ| ≤ (Real.log x) ^ S →
      ∀ ψ : ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ z ∉ Set.Icc a b₀, ψ z = 0) →
        (∀ z, ‖ψ z‖ ≤ (Real.log x) ^ F) → (∀ z, ‖deriv ψ z‖ ≤ (Real.log x) ^ F) →
      ∀ (k : ℕ) [NeZero k], (k : ℝ) ≤ (Real.log x) ^ C → ∀ h : ℤ,
      (∫ τ in Set.Icc (-((Real.log x) ^ S)) ((Real.log x) ^ S),
        ‖sourceComparisonCenteredMellinSum e ε x Y σ B ψ (giantCandidateGroup x ∘ i) t q b k h τ‖ ^ 2) ≤
        (Real.log x) ^ (-A) := by
  let A₁ := (A + S + 1) / 2
  filter_upwards [sourceComparisonCenteredMellinSum_lowTime_eventually.{u,v} e he heinj m hε hεq
    ha hab hB C S F A₁,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ))] with x hlow hL
  intro G _ i t ht q hq b hb Y σ hYlo hYhi hσ ψ hψ hs h0 h1 k _ hk h
  let L := Real.log x
  let T := L ^ S
  let f := sourceComparisonCenteredMellinSum e ε x Y σ B ψ (giantCandidateGroup x ∘ i) t q b k h
  have hL₀ : 0 < L := (by norm_num : (0:ℝ) < 2).trans_le hL
  have hT : 0 ≤ T := Real.rpow_nonneg hL₀.le _
  have hf := ((sourceComparisonCenteredMellinSum_continuous e ε x Y σ B ψ
    (giantCandidateGroup x ∘ i) t q b k h).norm.pow 2).integrableOn_Icc (μ := volume) (a := -T) (b := T)
  have hconst : IntegrableOn (fun _ : ℝ => (L ^ (-A₁)) ^ 2) (Set.Icc (-T) T) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hbound (τ : ℝ) (hτ : τ ∈ Set.Icc (-T) T) : ‖f τ‖ ^ 2 ≤ (L ^ (-A₁)) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact hlow i t ht q hq b hb Y σ τ hYlo hYhi hσ (abs_le.mpr hτ) ψ hψ hs h0 h1 k hk h
  calc
    _ ≤ ∫ _ in Set.Icc (-T) T, (L ^ (-A₁)) ^ 2 :=
      setIntegral_mono_on hf hconst measurableSet_Icc hbound
    _ = 2 * L ^ (-A - 1) := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith : -T ≤ T), smul_eq_mul]
      rw [show T - (-T) = 2 * L ^ S by unfold T; ring]
      rw [← Real.rpow_two (L ^ (-A₁)), ← Real.rpow_mul hL₀.le, mul_assoc, ← Real.rpow_add hL₀]
      congr 2
      unfold A₁
      ring
    _ ≤ _ := by
      rw [sub_eq_add_neg, Real.rpow_add hL₀, Real.rpow_neg_one]
      have hi : 2 * L⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv]
        exact (div_le_one hL₀).mpr hL
      calc
        _ = (2 * L⁻¹) * L ^ (-A) := by ring
        _ ≤ 1 * L ^ (-A) := mul_le_mul_of_nonneg_right hi (Real.rpow_nonneg hL₀.le _)
        _ = _ := one_mul _

end
end ArtinMatthews
