module

public import ArtinMatthews.SpectralHeatDiagonal
public import ArtinMatthews.SpectralABLBareIntegrability
public import ArtinMatthews.SpectralHeatEnergyWeight
public import ArtinMatthews.SpectralKLCoshIntegrability
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative transfer of literal real first moments to KL mass,
and removal of the Gaussian from the actual diagonal term. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ArtinMatthews

theorem spectralKLCosh_integral_norm_le (H : ℝ → ℂ) (G : ℝ → ℝ)
    (hH : Measurable H) (hG0 : ∀ t : ℝ, 0 < t → 0 ≤ G t)
    (hI : IntegrableOn (fun t => t*G t) (Ioi (0 : ℝ)))
    (hbound : ∀ t : ℝ, 0 < t → ‖H t‖ ≤ G t/Real.cosh (Real.pi*t)) :
    (∫ t, ‖H t‖ ∂spectralKLSpectralMeasure) ≤
      (2/Real.pi^2)*(∫ t in Ioi (0 : ℝ), t*G t) := by
  have hw := spectralKLPlancherelWeight_continuous.measurable
  have hp : ∀ t : ℝ, 0 < t → 0 ≤ spectralKLPlancherelWeight t :=
    fun t ht => (spectralKLPlancherelWeight_pos ht).le
  have hL := (spectralKLPositiveWeightMeasure_integrable_iff spectralKLPlancherelWeight
    (fun t => ‖H t‖) hw hp).mp (spectralKLCosh_integrable H G hH hG0 hI hbound).norm
  have hR := hI.const_mul (2/Real.pi^2)
  rw [spectralKLSpectralMeasure,spectralKLPositiveWeightMeasure_integral _ _ hw hp,← integral_const_mul]
  apply integral_mono_ae hL hR
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hGt := hG0 t ht0
  have hC : 0 ≤ 2/Real.pi^2*t*G t := by positivity
  change spectralKLPlancherelWeight t*‖H t‖ ≤ 2/Real.pi^2*(t*G t)
  calc
    _ ≤ spectralKLPlancherelWeight t*(G t/Real.cosh (Real.pi*t)) :=
      mul_le_mul_of_nonneg_left (hbound t ht0) (hp t ht0)
    _ = (2/Real.pi^2*t*G t)*(Real.sinh (Real.pi*t)/Real.cosh (Real.pi*t)) := by
      unfold spectralKLPlancherelWeight
      ring
    _ ≤ 2/Real.pi^2*t*G t :=
      mul_le_of_le_one_right hC ((div_le_one (Real.cosh_pos _)).mpr (Real.sinh_lt_cosh _).le)
    _ = _ := by ring

def spectralABLBareDiagonal (H : ℂ → ℂ) : ℂ :=
  ∫ t, H (t : ℂ) ∂spectralKLSpectralMeasure

theorem spectralABLHeatDiagonal_tendsto_bare (H : ℂ → ℂ)
    (hH : Integrable (fun t : ℝ => H (t : ℂ)) spectralKLSpectralMeasure) :
    Tendsto (spectralABLHeatDiagonal H) atTop (𝓝 (spectralABLBareDiagonal H)) := by
  unfold spectralABLHeatDiagonal spectralABLBareDiagonal
  apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => ‖H (t : ℂ)‖)
  · exact Eventually.of_forall (fun R => hH.aestronglyMeasurable.mul
      (show Measurable (fun t : ℝ => Complex.exp (-2*((t : ℂ)/(R : ℂ))^2)) from by fun_prop).aestronglyMeasurable)
  · exact Eventually.of_forall (fun R => Eventually.of_forall (fun t => by
      rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      rw [← spectralHeatEnergyWeight_principal]
      exact spectralHeatEnergyWeight_principal_norm_le R (1/4+t^2) (by nlinarith [sq_nonneg t])))
  · exact hH.norm
  · exact Eventually.of_forall (fun t => by
      have hg := spectralHeatEnergyWeight_tendsto (1/4+t^2)
      simp_rw [spectralHeatEnergyWeight_principal] at hg
      simpa only [mul_one] using tendsto_const_nhds.mul hg)

theorem spectralABLHeatDiagonal_norm_le (H : ℂ → ℂ)
    (hH : Integrable (fun t : ℝ => H (t : ℂ)) spectralKLSpectralMeasure) (R : ℝ) :
    ‖spectralABLHeatDiagonal H R‖ ≤ ∫ t, ‖H (t : ℂ)‖ ∂spectralKLSpectralMeasure := by
  let G : ℝ → ℂ := fun t => Complex.exp (-2*((t : ℂ)/(R : ℂ))^2)
  have hG : Measurable G := by dsimp only [G]; fun_prop
  have hb (t : ℝ) : ‖G t‖ ≤ 1 := by
    change ‖Complex.exp (-2*((t : ℂ)/(R : ℂ))^2)‖ ≤ 1
    rw [← spectralHeatEnergyWeight_principal]
    exact spectralHeatEnergyWeight_principal_norm_le R (1/4+t^2) (by nlinarith [sq_nonneg t])
  have hI : Integrable (fun t : ℝ => H (t : ℂ)*G t) spectralKLSpectralMeasure := by
    have hi := hH.bdd_mul hG.aestronglyMeasurable (ae_of_all _ hb)
    exact hi.congr (ae_of_all _ (fun t => mul_comm (G t) (H (t : ℂ))))
  change ‖∫ t, H (t : ℂ)*G t ∂spectralKLSpectralMeasure‖ ≤ _
  refine (norm_integral_le_integral_norm _).trans (integral_mono_ae hI.norm hH.norm ?_)
  exact ae_of_all _ (fun t => by
    change ‖H (t : ℂ)*G t‖ ≤ ‖H (t : ℂ)‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb t))

theorem spectralABLRegularHeatDiagonal_tendsto (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ) :
    Tendsto (spectralABLHeatDiagonal (spectralABLRegularCorrected T Δ)) atTop
      (𝓝 (spectralABLBareDiagonal (spectralABLRegularCorrected T Δ))) :=
  spectralABLHeatDiagonal_tendsto_bare _ (spectralABLRegularCorrected_integrable T Δ hT hΔ)

theorem spectralABLExceptionalHeatDiagonal_tendsto (a : ℝ) (A : ℕ) (hA : 3 ≤ A) :
    Tendsto (spectralABLHeatDiagonal (spectralABLExceptionalCorrected a A)) atTop
      (𝓝 (spectralABLBareDiagonal (spectralABLExceptionalCorrected a A))) :=
  spectralABLHeatDiagonal_tendsto_bare _ (spectralABLExceptionalCorrected_integrable a A hA)

end ArtinMatthews
