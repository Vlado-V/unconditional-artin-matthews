module

public import ArtinMatthews.SpectralStoneResolution
public import ArtinMatthews.SpectralStoneFrequency
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

/-! Exact compact forcing Plancherel in positive critical frequency, with
all full-energy orthogonal atoms retained. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal MatrixGroups
namespace ArtinMatthews

theorem gamma0CompactStonePlancherel_ennreal (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) :
    ENNReal.ofReal (‖gamma0SmoothSeedMass N ψ‖^2)=
      (∫⁻ t in Ioi 0,ENNReal.ofReal (gamma0StoneFrequencyDensity N ψ t))+
      ∑' l : gamma0StoneDiscreteEnergies N ψ Y,
        ENNReal.ofReal (‖gamma0AmbientSpectralAtomVector N (gamma0SmoothSeedMass N ψ) (l:ℝ)‖^2) := by
  have h := congrArg (fun μ : Measure ℝ => μ univ) (gamma0AmbientSpectralMeasure_resolved N ψ Y)
  change gamma0AmbientSpectralMeasure N (gamma0SmoothSeedMass N ψ) univ=
    (gamma0StoneContinuousMeasure N ψ Y+
      Measure.sum (fun l : gamma0StoneDiscreteEnergies N ψ Y =>
        ENNReal.ofReal (‖gamma0AmbientSpectralAtomVector N (gamma0SmoothSeedMass N ψ) (l:ℝ)‖^2) •
          Measure.dirac (l:ℝ))) univ at h
  simpa only [gamma0AmbientSpectralMeasure_univ,Measure.add_apply,Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one,
    gamma0StoneContinuousMeasure_univ_frequency N ψ Y] using h

theorem gamma0StoneFrequencyDensity_integrableOn (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) :
    IntegrableOn (gamma0StoneFrequencyDensity N ψ) (Ioi 0) := by
  refine ⟨(gamma0StoneFrequencyDensity_aemeasurable N ψ Y).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (gamma0StoneFrequencyDensity_nonneg N ψ))]
  have h := gamma0CompactStonePlancherel_ennreal N ψ Y
  apply lt_of_le_of_lt (le_add_right le_rfl)
  rw [← h]
  exact ENNReal.ofReal_lt_top

theorem gamma0CompactStonePlancherel (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) :
    ‖gamma0SmoothSeedMass N ψ‖^2=
      (∫ t in Ioi 0,gamma0StoneFrequencyDensity N ψ t)+
      ∑' l : gamma0StoneDiscreteEnergies N ψ Y,
        ‖gamma0AmbientSpectralAtomVector N (gamma0SmoothSeedMass N ψ) (l:ℝ)‖^2 := by
  have h := gamma0CompactStonePlancherel_ennreal N ψ Y
  let A := ∫⁻ t in Ioi 0,ENNReal.ofReal (gamma0StoneFrequencyDensity N ψ t)
  let B := ∑' l : gamma0StoneDiscreteEnergies N ψ Y,
    ENNReal.ofReal (‖gamma0AmbientSpectralAtomVector N (gamma0SmoothSeedMass N ψ) (l:ℝ)‖^2)
  have hfinite : A+B<∞ := by
    rw [← h]
    exact ENNReal.ofReal_lt_top
  have hA : A≠∞ := ne_of_lt (lt_of_le_of_lt (le_add_right le_rfl) hfinite)
  have hB : B≠∞ := ne_of_lt (lt_of_le_of_lt (le_add_left le_rfl) hfinite)
  have hInt := gamma0StoneFrequencyDensity_integrableOn N ψ Y
  have hnonneg := ae_of_all (volume.restrict (Ioi 0)) (gamma0StoneFrequencyDensity_nonneg N ψ)
  have hAn : 0≤∫ t in Ioi 0,gamma0StoneFrequencyDensity N ψ t := integral_nonneg_of_ae hnonneg
  have h' := congrArg ENNReal.toReal h
  change (ENNReal.ofReal (‖gamma0SmoothSeedMass N ψ‖^2)).toReal=(A+B).toReal at h'
  rw [ENNReal.toReal_add hA hB,ENNReal.toReal_ofReal (sq_nonneg _)] at h'
  have hAr : A.toReal=∫ t in Ioi 0,gamma0StoneFrequencyDensity N ψ t := by
    rw [← ENNReal.toReal_ofReal hAn,ofReal_integral_eq_lintegral_ofReal hInt hnonneg]
  have hBr : B.toReal=∑' l : gamma0StoneDiscreteEnergies N ψ Y,
      ‖gamma0AmbientSpectralAtomVector N (gamma0SmoothSeedMass N ψ) (l:ℝ)‖^2 := by
    unfold B
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    exact tsum_congr (fun _ => ENNReal.toReal_ofReal (sq_nonneg _))
  rwa [hAr,hBr] at h'

end ArtinMatthews
