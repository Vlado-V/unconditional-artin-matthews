module

public import ArtinMatthews.GiantActualRoughSieve
public import ArtinMatthews.PrimeExtractionWeightBounds
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

/-! Uniform boundedness of the actual cutoff, marking array, and core
weight on the finite extraction interval. -/

namespace ArtinMatthews

open Filter

noncomputable def markedExtractionWeight {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℂ :=
  (Φ (((n - 1 : ℕ) : ℝ) / x) : ℂ) * (literalMarkedArrayWeight e x (n - 1) : ℂ) * G x (n - 1)

theorem markedExtractionWeight_bound {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (G : ℝ → ℕ → ℂ)
    {CG : ℝ} (hCG : 0 ≤ CG) (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T * x →
      ‖markedExtractionWeight e G Φ x n‖ ≤ C := by
  obtain ⟨CΦ, hCΦ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hΦ.continuousOn : ContinuousOn Φ (Set.Icc 0 T))
  have hCΦ0 : 0 ≤ CΦ := (norm_nonneg (Φ 0)).trans (hCΦ 0 ⟨le_rfl, hT⟩)
  let W := (2 / Real.log 2) ^ Fintype.card ι
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  refine ⟨CΦ * W * CG, mul_nonneg (mul_nonneg hCΦ0 hW0) hCG, ?_⟩
  filter_upwards [literalMarkedArrayWeight_bound_eventually e he, hG,
    eventually_gt_atTop (0 : ℝ)] with x hW hGx hx
  intro n hnT
  have harg : ((n - 1 : ℕ) : ℝ) / x ∈ Set.Icc 0 T :=
    ⟨div_nonneg (Nat.cast_nonneg _) hx.le,
      (div_le_iff₀ hx).mpr ((Nat.cast_le.mpr (Nat.sub_le n 1)).trans hnT)⟩
  have hphi : ‖(Φ (((n - 1 : ℕ) : ℝ) / x) : ℂ)‖ ≤ CΦ := by
    simpa only [Complex.norm_real] using hCΦ _ harg
  have hweight : ‖(literalMarkedArrayWeight e x (n - 1) : ℂ)‖ ≤ W := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (literalMarkedArrayWeight_nonneg e x (n - 1))] using hW (n - 1)
  unfold markedExtractionWeight
  simp only [norm_mul]
  exact mul_le_mul (mul_le_mul hphi hweight (norm_nonneg _) hCΦ0)
    (hGx _) (norm_nonneg _) (mul_nonneg hCΦ0 hW0)

end ArtinMatthews
