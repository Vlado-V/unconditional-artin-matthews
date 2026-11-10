module

public import ArtinMatthews.SpectralAmbientGreenMoments
public import ArtinMatthews.SpectralStoneFrequency
public import ArtinMatthews.SpectralStoneResolution
public import ArtinMatthews.SpectralStoneFrequencyMeasure
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual weighted Green moments of a compact automorphic seed, with
the genuine Eisenstein continuum and all energy atoms retained. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace ArtinMatthews

theorem gamma0CompactSpectralMeasure_integral_resolved (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ)
    (a : ℝ → ℂ) (ha : Integrable a (gamma0AmbientSpectralMeasure N (gamma0SmoothSeedMass N ψ))) :
    (∫ l,a l ∂gamma0AmbientSpectralMeasure N (gamma0SmoothSeedMass N ψ))=
      (∫ t in Ioi 0,(gamma0StoneFrequencyDensity N ψ t:ℂ)*a (spectralStoneEnergyFromFrequency t))+
      ∑' l : gamma0StoneDiscreteEnergies N ψ Y,
        (‖gamma0AmbientSpectralAtomVector N (gamma0SmoothSeedMass N ψ) (l:ℝ)‖^2:ℝ) • a (l:ℝ) := by
  let D := gamma0StoneDiscreteEnergies N ψ Y
  let _ : Countable D := (gamma0StoneDiscreteEnergies_countable N ψ Y).to_subtype
  have hi := ha
  rw [gamma0AmbientSpectralMeasure_resolved N ψ Y] at hi
  obtain ⟨hc,hd⟩ := integrable_add_measure.mp hi
  rw [gamma0AmbientSpectralMeasure_resolved N ψ Y,integral_add_measure hc hd,
    gamma0StoneContinuousMeasure_integral_frequency N ψ Y a hc,
    integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
  congr 1
  apply tsum_congr
  intro l
  rw [ENNReal.toReal_ofReal (sq_nonneg _)]

theorem gamma0CompactGreen_power_spectral_moment (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) (n : ℕ) (hn : n≠0) :
    inner ℂ (gamma0SmoothSeedMass N ψ) (((gamma0Green N)^n) (gamma0SmoothSeedMass N ψ))=
      (∫ t in Ioi 0,(gamma0StoneFrequencyDensity N ψ t:ℂ)*
        gamma0EnergyGreenWeight (spectralStoneEnergyFromFrequency t)^n)+
      ∑' l : gamma0StoneDiscreteEnergies N ψ Y,
        (‖gamma0AmbientSpectralAtomVector N (gamma0SmoothSeedMass N ψ) (l:ℝ)‖^2:ℝ) •
          (gamma0EnergyGreenWeight (l:ℝ)^n) := by
  rw [← gamma0AmbientSpectralMeasure_green_power N (gamma0SmoothSeedMass N ψ) n hn]
  exact gamma0CompactSpectralMeasure_integral_resolved N ψ Y _
    (gamma0AmbientSpectralMeasure_green_power_integrable N (gamma0SmoothSeedMass N ψ) n)

end ArtinMatthews
