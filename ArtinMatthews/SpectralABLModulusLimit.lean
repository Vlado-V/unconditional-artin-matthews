module

public import ArtinMatthews.SpectralBareModulusSeries
public import ArtinMatthews.SpectralHeatSpectralPairing
public import ArtinMatthews.SpectralABLBareDiagonal
public import ArtinMatthews.SpectralABLBareIntegrability
public import ArtinMatthews.SpectralNativeHeatTrace
public import ArtinMatthews.SpectralWeylABLBound
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

/-! Actual source-window removal of the Gaussian from the full
true-width modulus sum, and bounded native diagonal spectral tests. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups Topology
namespace ArtinMatthews

theorem spectralABLRegularHeatKernel_small_bound (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ)
    (m n : ℤ) (X₀ : ℝ) (hX₀ : 0 < X₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ X : ℝ, 0 < X → X ≤ X₀ →
      ‖spectralABLHeatKernel (spectralABLRegularCorrected T Δ) R m n X‖ ≤ C*X^(1/4 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := spectralABLRegular_JKGaussian_small_bound T Δ hT hΔ hX₀
  refine ⟨C,hC.le,?_⟩
  intro R hR X hX hXX
  by_cases hmn : 0 < m*n
  · simpa only [spectralABLHeatKernel,spectralWeylIntegerSignMultiplier,ite_eq_left hmn] using
      (hb R X hR hX hXX).1
  · simpa only [spectralABLHeatKernel,spectralWeylIntegerSignMultiplier,ite_eq_right hmn] using
      (hb R X hR hX hXX).2

theorem spectralABLExceptionalHeatKernel_small_bound (a : ℝ) (A : ℕ) (hA : 2 ≤ A)
    (m n : ℤ) (X₀ : ℝ) (hX₀ : 0 < X₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ X : ℝ, 0 < X → X ≤ X₀ →
      ‖spectralABLHeatKernel (spectralABLExceptionalCorrected a A) R m n X‖ ≤ C*X^(1/4 : ℝ) := by
  obtain ⟨C,hC,hb⟩ := spectralABLExceptional_JKGaussian_small_bound a hA hX₀
  refine ⟨C,hC.le,?_⟩
  intro R hR X hX hXX
  by_cases hmn : 0 < m*n
  · simpa only [spectralABLHeatKernel,spectralWeylIntegerSignMultiplier,ite_eq_left hmn] using
      (hb R X hR hX hXX).1
  · simpa only [spectralABLHeatKernel,spectralWeylIntegerSignMultiplier,ite_eq_right hmn] using
      (hb R X hR hX hXX).2

theorem gamma0TrueWidthRegularHeatSeries_tendsto_bare (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ) :
    Summable (fun c : Ioi (0 : ℕ) => gamma0TrueWidthBareFibre N r s c m n
      (spectralABLRegularCorrected T Δ)) ∧
      Tendsto (fun R : ℝ => ∑' c : Ioi (0 : ℕ), gamma0TrueWidthHeatFibre N r s c m n
        (spectralABLRegularCorrected T Δ) R) atTop
        (𝓝 (∑' c : Ioi (0 : ℕ), gamma0TrueWidthBareFibre N r s c m n
          (spectralABLRegularCorrected T Δ))) :=
  gamma0TrueWidthHeatSeries_tendsto_bare N r s m n hm hn _
    (spectralABLRegularCorrected_integrable T Δ hT hΔ)
    (spectralABLRegularHeatKernel_small_bound T Δ hT hΔ m n)

theorem gamma0TrueWidthExceptionalHeatSeries_tendsto_bare (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (a : ℝ) (A : ℕ) (hA : 3 ≤ A) :
    Summable (fun c : Ioi (0 : ℕ) => gamma0TrueWidthBareFibre N r s c m n
      (spectralABLExceptionalCorrected a A)) ∧
      Tendsto (fun R : ℝ => ∑' c : Ioi (0 : ℕ), gamma0TrueWidthHeatFibre N r s c m n
        (spectralABLExceptionalCorrected a A) R) atTop
        (𝓝 (∑' c : Ioi (0 : ℕ), gamma0TrueWidthBareFibre N r s c m n
          (spectralABLExceptionalCorrected a A))) :=
  gamma0TrueWidthHeatSeries_tendsto_bare N r s m n hm hn _
    (spectralABLExceptionalCorrected_integrable a A hA)
    (spectralABLExceptionalHeatKernel_small_bound a A (by omega) m n)

theorem gamma0TrueWidthHeatSeries_uniform_norm_bound (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (H : ℂ → ℂ)
    (hK : ∀ X₀ : ℝ, 0 < X₀ → ∃ D : ℝ, 0 ≤ D ∧
      ∀ R : ℝ, 1 ≤ R → ∀ X : ℝ, 0 < X → X ≤ X₀ →
        ‖spectralABLHeatKernel H R m n X‖ ≤ D*X^(1/4 : ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R : ℝ, 1 ≤ R →
      ‖∑' c : Ioi (0 : ℕ), gamma0TrueWidthHeatFibre N r s c m n H R‖ ≤ D := by
  obtain ⟨L,hL0,hL⟩ := gamma0TrueWidthHeatFibre_uniform_bare_bound N r s m n hm hn H hK
  let g : Ioi (0 : ℕ) → ℝ := fun c => L/(c.val : ℝ)^(5/4 : ℝ)
  have hp : Summable (fun c : ℕ => 1/(c : ℝ)^(5/4 : ℝ)) := Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hs : Summable g := by
    simpa only [g,mul_one_div,Function.comp_def] using! (hp.mul_left L).subtype (Ioi (0 : ℕ))
  have hg (c : Ioi (0 : ℕ)) : 0 ≤ g c := div_nonneg hL0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨∑' c, g c,tsum_nonneg hg,?_⟩
  intro R hR
  have hS : Summable (fun c : Ioi (0 : ℕ) => ‖gamma0TrueWidthHeatFibre N r s c m n H R‖) := by
    apply hs.of_norm_bounded
    intro c
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hL R hR c
  exact (norm_tsum_le_tsum_norm hS).trans (hS.tsum_le_tsum (hL R hR) hs)

theorem gamma0HeatRegular_source_diagonal_uniform (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (T ε : ℝ) (hT : 0 < T) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R : ℝ, 1 ≤ R →
      ‖gamma0HeatSourceSpectralSide N (spectralABLRegularEnergyTest T (T^(1-ε)) hT
        (Real.rpow_pos_of_pos hT _)) r r Y hY n n hn hn R‖ ≤ D := by
  let H := spectralABLRegularCorrected T (T^(1-ε))
  have hΔ := Real.rpow_pos_of_pos hT (1-ε)
  have hI := spectralABLRegularCorrected_integrable T (T^(1-ε)) hT hΔ
  obtain ⟨C,hC,hbound⟩ := gamma0TrueWidthHeatSeries_uniform_norm_bound N r r n n hn hn H
    (spectralABLRegularHeatKernel_small_bound T (T^(1-ε)) hT hΔ n n)
  have hmass : 0 ≤ ∫ t : ℝ, ‖H (t : ℂ)‖ ∂spectralKLSpectralMeasure := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨(1/4)*((∫ t : ℝ, ‖H (t : ℂ)‖ ∂spectralKLSpectralMeasure)+C),by positivity,?_⟩
  intro R hR
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hquarter : ‖(1/4 : ℂ)‖ = (1/4 : ℝ) := by norm_num [norm_div]
  rw [gamma0HeatRegular_sameCusp_source_trace N r Y hY n n hn hn T ε R hT hR0,
    ite_eq_left (rfl : n = n),norm_mul,hquarter]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
    (add_le_add (spectralABLHeatDiagonal_norm_le H hI R) (hbound R hR))) (by norm_num)

theorem gamma0HeatExceptional_source_diagonal_uniform (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (a : ℝ) (A : ℕ) (hA : 3 ≤ A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R : ℝ, 1 ≤ R →
      ‖gamma0HeatSourceSpectralSide N (spectralABLExceptionalEnergyTest a A (by omega))
        r r Y hY n n hn hn R‖ ≤ D := by
  let H := spectralABLExceptionalCorrected a A
  have hI := spectralABLExceptionalCorrected_integrable a A hA
  obtain ⟨C,hC,hbound⟩ := gamma0TrueWidthHeatSeries_uniform_norm_bound N r r n n hn hn H
    (spectralABLExceptionalHeatKernel_small_bound a A (by omega) n n)
  have hmass : 0 ≤ ∫ t : ℝ, ‖H (t : ℂ)‖ ∂spectralKLSpectralMeasure := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨(1/4)*((∫ t : ℝ, ‖H (t : ℂ)‖ ∂spectralKLSpectralMeasure)+C),by positivity,?_⟩
  intro R hR
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hquarter : ‖(1/4 : ℂ)‖ = (1/4 : ℝ) := by norm_num [norm_div]
  rw [gamma0HeatExceptional_sameCusp_source_trace N r Y hY n n hn hn a A R (by omega) hR0,
    ite_eq_left (rfl : n = n),norm_mul,hquarter]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
    (add_le_add (spectralABLHeatDiagonal_norm_le H hI R) (hbound R hR))) (by norm_num)

end ArtinMatthews
