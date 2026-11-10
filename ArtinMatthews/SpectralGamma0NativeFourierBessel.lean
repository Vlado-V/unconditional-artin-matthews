module

public import ArtinMatthews.SpectralCuspTwoCellFourier
public import ArtinMatthews.SpectralGamma0CuspActual
public import Mathlib.Analysis.RCLike.Sqrt
public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralGamma0EllipticEigenPlane
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
public import ArtinMatthews.SpectralHorizontalPeriodMeasurableFibers
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

/-! The native cuspidal spectral basis has the actual K-Bessel Fourier
coefficients. Smoothness, local periodicity, the eigen-equation, and both
energy hypotheses are all discharged by the actual completed constructions. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0FullCuspidalSpectralBasis_fourier_bessel_ae
    (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    ∃ a : ℂ, gamma0CuspFourierCoefficient N r Y hY n
        (gamma0FullCuspidalSpectralBasis N i).val =ᵐ[volume.restrict (Ioi Y)]
      fun y => a * ((Real.sqrt y : ℂ) * OAI.CubicEisenstein.schlafliBesselK
        (Complex.sqrt (1 / 4 - (gamma0AllHeightGradientSpectralValue N i : ℂ)))
        (|cuspFourierFrequency (N : ℝ) n| * y)) := by
  obtain ⟨u, hu, hrep, hp, hEq⟩ :=
    gamma0FullCuspidalSpectralBasis_plane_smooth_periodic_classical N i r Y hY
  have hmass : gamma0EnergyInclusion N (gamma0AllHeightSpectralEnergy N i).val =
      (gamma0FullCuspidalSpectralBasis N i).val :=
    (gamma0AllHeightSpectralEnergy_mass_ambient N i).trans
      (gamma0FullCuspidalSpectralBasis_coe N i).symm
  have h := gamma0CuspLocalFourier_bessel_ae N r Y hY n hn
    (gamma0AllHeightSpectralEnergy N i).val u hu (by rw [hmass]; exact hrep)
    (fun x t hx hxt ht => hp (x, t) ⟨hx, hxt, ht⟩)
    (gamma0AllHeightGradientSpectralValue N i) hEq
  simpa only [hmass] using h

theorem gamma0FullCuspidalSpectralBasis_twoCell_fourier_bessel_ae
    (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    ∃ a : ℂ, gamma0CuspTwoCellFourierCoefficient N r Y hY n
        (gamma0FullCuspidalSpectralBasis N i).val =ᵐ[volume.restrict (Ioi Y)]
      fun y => a * ((Real.sqrt y : ℂ) * OAI.CubicEisenstein.schlafliBesselK
        (Complex.sqrt (1 / 4 - (gamma0AllHeightGradientSpectralValue N i : ℂ)))
        (|cuspFourierFrequency (N : ℝ) n| * y)) := by
  obtain ⟨a, ha⟩ := gamma0FullCuspidalSpectralBasis_fourier_bessel_ae N i r Y hY n hn
  refine ⟨a, ?_⟩
  have htwo : gamma0CuspTwoCellFourierCoefficient N r Y hY n
      (gamma0FullCuspidalSpectralBasis N i).val =ᵐ[volume.restrict (Ioi Y)]
      gamma0CuspFourierCoefficient N r Y hY n
        (gamma0FullCuspidalSpectralBasis N i).val :=
    (spectralHorizontal_cuspVertical_ae_iff hY).mp
    (gamma0CuspTwoCellFourierCoefficient_ae N r Y hY n
      (gamma0FullCuspidalSpectralBasis N i).val)
  exact Filter.EventuallyEq.trans htwo ha

end ArtinMatthews
