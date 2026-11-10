module

public import ArtinMatthews.GiantComparisonCellMellin
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

/-! The smooth physical cutoff preserves any prescribed logarithmic
saving, with the omitted Mellin frequencies estimated in absolute value. -/
namespace ArtinMatthews
open Filter MeasureTheory Finset
open scoped BigOperators FourierTransform ContDiff SchwartzMap Topology
noncomputable section

theorem giantComparisonNatCutoffSum_log_saving
    (Ψ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a) (hsupp : Function.support Ψ ⊆ Set.Icc a b)
    (hΨ : ContDiff ℝ ∞ Ψ) (D A : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {I K : Type} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K],
      ∀ (P : I → Finset ℕ) (R : K → Finset ℕ),
      (∀ i p, p ∈ P i → p.Prime) → (∀ j p, p ∈ R j → p.Prime) →
      (∀ i, 0 < bandReciprocalMass (P i)) → (∀ j, 0 < bandReciprocalMass (R j)) →
      ∀ (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ),
      (∀ z, ‖f z‖ ≤ 1) → (∀ z, ‖g z‖ ≤ 1) →
      ∀ (S T : Finset ℕ) (U V : ℕ → ℂ), (∀ w ∈ S, 0 < w) →
      ∀ (x Y : ℝ), 0 < x → 0 ≤ Y →
      (∑ w ∈ S, ‖U w‖^2) ≤ Y*L^D → (∑ v ∈ T, ‖V v‖^2) ≤ Y*L^D →
      (∀ t ∈ Set.Icc (-L) L, ‖giantComparisonNatShiftSum P R
        (fun u => f u*primeExtractionMellinPhase (-t) (idealSelectedProduct u))
        (fun v => g v*primeExtractionMellinPhase (-t) (idealSelectedProduct v))
        S T (fun w => U w*primeExtractionMellinPhase (-t) (w : ℝ)) V‖ ≤
          Y*L^(-A-1)) →
      ‖giantComparisonNatCutoffSum P R f g S T U V Ψ x‖ ≤ Y*L^(-A) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (D+A+1)
  let F : SchwartzMap ℝ ℂ := 𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)
  let K₀ := ∫ t : ℝ, ‖F t‖
  let Kₙ := ∫ t : ℝ, |t|^n*‖F t‖
  have hKₙ : 0 ≤ Kₙ := integral_nonneg fun t => by positivity
  filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (K₀+Kₙ)] with L hL hK
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  intro I K _ _ _ _ P R hP hR hVP hVR f g hf hg S T U V hS x Y hx hY hU hV hbound
  have hLpow : 0 < L^D := Real.rpow_pos_of_pos hL0 _
  have hYpow : 0 ≤ Y*L^D := mul_nonneg hY hLpow.le
  have hUV : Real.sqrt ((∑ w ∈ S, ‖U w‖^2)*(∑ v ∈ T, ‖V v‖^2)) ≤ Y*L^D := by
    rw [← Real.sqrt_mul_self hYpow]
    exact Real.sqrt_le_sqrt (mul_le_mul hU hV (sum_nonneg fun _ _ => sq_nonneg _) hYpow)
  have htail : Kₙ/L^n*(Y*L^D) ≤ Kₙ*(Y*L^(-A-1)) := by
    rw [← Real.rpow_natCast, div_eq_mul_inv, ← Real.rpow_neg hL0.le]
    calc
      _ = Kₙ*(Y*L^(D-(n:ℝ))) := by
        rw [sub_eq_add_neg, Real.rpow_add hL0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) hY) hKₙ
  have hmain := giantComparisonNatCutoffSum_mellin_bound P R hP hR hVP hVR f g hf hg S T U V hS
    Ψ ha hsupp hΨ hx hL0 (mul_nonneg hY (Real.rpow_nonneg hL0.le _)) n hbound
  calc
    _ ≤ K₀*(Y*L^(-A-1)) + Kₙ/L^n*
        Real.sqrt ((∑ w ∈ S, ‖U w‖^2)*(∑ v ∈ T, ‖V v‖^2)) := hmain
    _ ≤ K₀*(Y*L^(-A-1)) + Kₙ*(Y*L^(-A-1)) :=
      add_le_add le_rfl ((mul_le_mul_of_nonneg_left hUV (div_nonneg hKₙ (by positivity))).trans htail)
    _ = (K₀+Kₙ)*(Y*L^(-A-1)) := by ring
    _ ≤ L*(Y*L^(-A-1)) :=
      mul_le_mul_of_nonneg_right hK (mul_nonneg hY (Real.rpow_nonneg hL0.le _))
    _ = Y*L^(-A) := by
      calc
        _ = Y*(L^(1:ℝ)*L^(-A-1)) := by rw [Real.rpow_one]; ring
        _ = _ := by rw [← Real.rpow_add hL0, show 1+(-A-1) = -A by ring]

end
end ArtinMatthews
