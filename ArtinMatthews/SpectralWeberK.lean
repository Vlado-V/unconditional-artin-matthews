module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralMellinUniqueness
public import ArtinMatthews.SpectralWeberKClosedMellin
public import ArtinMatthews.SpectralWeberKMellin
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

/-! Genuine Gaussian Weber evaluation of the doubled-order K integral,
deduced from actual Mellin integrals and uniqueness. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralWeberK_evaluation {ν : ℂ} (hν : |ν.re| < 1/2)
    {p : ℝ} (hp : 0 < p) :
    (∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(x : ℂ)^2)*schlafliBesselK (2*ν) x) =
      ((Real.sqrt Real.pi : ℂ)/(4*Complex.cos ((Real.pi : ℂ)*ν)))*
        ((p : ℂ)^(-(1/2 : ℂ))*(Complex.exp (((1/8 : ℝ)/p : ℝ) : ℂ)*
          schlafliBesselK ν ((1/8 : ℝ)/p))) := by
  let σ : ℝ := (1/2-|ν.re|)/2
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσstrip : σ+|ν.re| < 1/2 := by dsimp [σ]; linarith
  apply spectral_mellin_unique (spectralWeberKTransform ν) (spectralWeberKClosed ν) σ
  · intro t
    exact spectralWeberK_mellin_convergent ν _ (by simpa using hσ) (by simpa using hσstrip)
  · intro t
    exact spectralWeberKClosed_mellin_convergent ν _ (by simpa using hσ) (by simpa using hσstrip)
  · intro t
    rw [spectralWeberK_mellin ν _ (by simpa using hσ) (by simpa using hσstrip),
      spectralWeberKClosed_mellin ν _ (by simpa using hσ) (by simpa using hσstrip)]
  · exact hp
  · exact spectralWeberK_continuousAt hν hp
  · exact spectralWeberKClosed_continuousAt ν hp

end ArtinMatthews
