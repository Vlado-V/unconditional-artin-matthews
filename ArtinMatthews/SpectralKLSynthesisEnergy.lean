module

public import ArtinMatthews.SpectralKLSynthesis
public import ArtinMatthews.SpectralKLRegularizedPairing
public import ArtinMatthews.SpectralMellinEnergyBoundary
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact spectral synthesis energy, with the Mellin
regularization removed by Fatou and dominated convergence. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectral_complex_mul_star (z : ℂ) : z*star z = ((‖z‖^2 : ℝ) : ℂ) := by
  simpa only [starRingEnd_apply,Complex.ofReal_pow] using Complex.mul_conj' z

theorem spectralKLSynthesis_regularized_energy_limit (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    Tendsto (fun ε : ℝ => ∫ x in Ioi (0 : ℝ), x^(ε-1)*‖spectralKLSynthesis f x‖^2)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t : ℝ, (Real.pi^2/(2*t*Real.sinh (Real.pi*t)))*‖f t‖^2)) := by
  have hgs : tsupport (fun t => star (f t)) = tsupport f := by
    unfold tsupport
    congr 1
    ext t
    simp [Function.mem_support]
  have hgc : HasCompactSupport (fun t => star (f t)) := by
    change IsCompact _
    rw [hgs]
    exact hfc.isCompact
  have hgp : tsupport (fun t => star (f t)) ⊆ Ioi (0 : ℝ) := by rw [hgs]; exact hfp
  have hl := spectralKLSynthesis_regularized_pairing_limit f (fun t => star (f t))
    hf (continuous_star.comp hf) hfc hgc hfp hgp
  have hreg (ε : ℝ) :
      (∫ x in Ioi (0 : ℝ), (x^(ε-1) : ℝ)*
        (spectralKLSynthesis f x*spectralKLSynthesis (fun t => star (f t)) x)) =
      ((∫ x in Ioi (0 : ℝ), x^(ε-1)*‖spectralKLSynthesis f x‖^2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    rw [spectralKLSynthesis_conj,spectral_complex_mul_star,Complex.ofReal_mul]
  have hspec : (∫ t : ℝ, ((Real.pi^2/(2*t*Real.sinh (Real.pi*t)) : ℝ) : ℂ)*(f t*star (f t))) =
      ((∫ t : ℝ, (Real.pi^2/(2*t*Real.sinh (Real.pi*t)))*‖f t‖^2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with t
    rw [spectral_complex_mul_star,Complex.ofReal_mul]
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hl
  simpa only [Function.comp_def,hreg,hspec,Complex.ofReal_re] using hr

theorem spectralKLSynthesis_energy (f : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    IntegrableOn (fun x : ℝ => x^(-1 : ℝ)*‖spectralKLSynthesis f x‖^2) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), x^(-1 : ℝ)*‖spectralKLSynthesis f x‖^2) =
        ∫ t : ℝ, (Real.pi^2/(2*t*Real.sinh (Real.pi*t)))*‖f t‖^2 := by
  exact spectral_mellin_energy_boundary (fun x => ‖spectralKLSynthesis f x‖^2)
    (fun _ _ => sq_nonneg _) (spectralKLSynthesis_regularized_energy_integrable f hf hfc) _
    (spectralKLSynthesis_regularized_energy_limit f hf hfc hfp)

end ArtinMatthews
