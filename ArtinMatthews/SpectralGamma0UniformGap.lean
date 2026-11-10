module

public import ArtinMatthews.SpectralGamma0CuspEigenfunctions
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralInfinityCuspAmplitude
public import ArtinMatthews.SpectralInfinityNativeAmplitudeNonzero
public import ArtinMatthews.SpectralMixedCuspGap
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual trivial-character Gamma0 cusp spectrum has a uniform
3/16 lower bound. The level and mode are fixed before the small-scale limit. -/
noncomputable section
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0AllHeightGradientSpectralValue_ge_three_sixteenths (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    3/16 ≤ gamma0AllHeightGradientSpectralValue N i := by
  have h (M : ℕ) [NeZero M] (hM : M = 1*N) (j : Gamma0AllHeightSpectralIndex M) :
      3/16 ≤ gamma0AllHeightGradientSpectralValue M j := by
    subst M
    obtain ⟨n,hn,hAmp⟩ := gamma0InfinityNativeBesselAmplitude_exists_ne_zero (1*N) j 1 one_pos
    have hStep : gamma0CuspFrequencyStep (1*N) (1 : SL(2, ℤ)) = 1*N := by
      simpa only [gamma0CuspTrueWidth_identity, one_mul] using
        gamma0CuspFrequencyStep_mul_width (1*N) (1 : SL(2, ℤ))
    have hinfinity :
        gamma0CuspBesselAmplitude (1*N) j 1 1 one_pos
          ((gamma0CuspFrequencyStep (1*N) 1 : ℤ)*n)
          (gamma0CuspFrequencyStep_mul_ne_zero (1*N) 1 hn) ≠ 0 := by
      simpa only [hStep] using hAmp
    have hm (a : SL(2, ℤ)) (ha : a = gamma0CuspOneOver (1*N)) :
        gamma0CuspBesselAmplitude (1*N) j a 1 one_pos
          ((gamma0CuspFrequencyStep (1*N) a : ℤ)*n)
          (gamma0CuspFrequencyStep_mul_ne_zero (1*N) a hn) ≠ 0 := by
      subst a
      rw [gamma0CuspBesselAmplitude_oneOver_trueFrequency_eq_identity (1*N) j 1 one_pos n hn]
      exact hinfinity
    exact gamma0MixedCusp_spectralValue_ge_three_sixteenths_of_amplitude
      1 N (Nat.coprime_one_left N) j n hn (hm (gamma0CuspOneOver N) (by rw [one_mul]))
  exact h N (one_mul N).symm i

theorem gamma0AllHeightGradientSpectralGap_uniform :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N),
      δ ≤ gamma0AllHeightGradientSpectralValue N i :=
  ⟨3/16, by norm_num, gamma0AllHeightGradientSpectralValue_ge_three_sixteenths⟩

end ArtinMatthews
