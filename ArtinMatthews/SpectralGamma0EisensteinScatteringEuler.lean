module

public import ArtinMatthews.SpectralGamma0EisensteinConstantTerm
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import ArtinMatthews.SpectralEisensteinNormalizedLevelFactor
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

/-! The actual infinity scattering coefficient and actual constant term with finite level factors. -/
noncomputable section
open MeasureTheory
namespace ArtinMatthews

theorem gamma0EisensteinScatteringInfinity_euler (N : ℕ) (hN : 0<N) (s : ℂ) (hs : 1<s.re) :
    gamma0EisensteinScatteringInfinity N s =
      ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*
        (riemannZeta (2*s-1)/riemannZeta (2*s))*(N:ℂ)^(1-2*s)*
          ∏ p ∈ N.primeFactors, ((1-(p:ℂ)⁻¹)/(1-(p:ℂ)^(-2*s))) := by
  unfold gamma0EisensteinScatteringInfinity
  rw [gamma0EisensteinTotientSeries_euler_factors N hN s hs]
  ring

theorem gamma0Eisenstein_infinity_constant_term_euler (N : ℕ) (hN : 0<N) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) :
    (∫ x in (0:ℝ)..1, gamma0EisensteinSlice N s y hy x) = (y:ℂ)^s+
      (y:ℂ)^(1-s)*((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*
        (riemannZeta (2*s-1)/riemannZeta (2*s))*(N:ℂ)^(1-2*s)*
          ∏ p ∈ N.primeFactors, ((1-(p:ℂ)⁻¹)/(1-(p:ℂ)^(-2*s))) := by
  rw [gamma0Eisenstein_infinity_constant_term N s hs y hy,
    gamma0EisensteinScatteringInfinity_euler N hN s hs]
  ring

theorem gamma0EisensteinFourier_zero_euler (N : ℕ) (hN : 0<N) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) :
    gamma0EisensteinFourierCoefficient N s y hy 0 = (y:ℂ)^s+
      (y:ℂ)^(1-s)*((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*
        (riemannZeta (2*s-1)/riemannZeta (2*s))*(N:ℂ)^(1-2*s)*
          ∏ p ∈ N.primeFactors, ((1-(p:ℂ)⁻¹)/(1-(p:ℂ)^(-2*s))) := by
  rw [gamma0EisensteinFourier_zero,gamma0Eisenstein_infinity_constant_term_euler N hN s hs y hy]

end ArtinMatthews
