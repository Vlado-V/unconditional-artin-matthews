module

public import ArtinMatthews.SpectralEisensteinEulerDenominator
public import ArtinMatthews.SpectralGamma0EisensteinTotientSeries
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import ArtinMatthews.SpectralEisensteinLevelEuler
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

/-! The conventional finite Euler factors, including the exact power of the fixed level. -/
noncomputable section
namespace ArtinMatthews

theorem spectralTotient_complex_product (N : ℕ) :
    (N.totient:ℂ)=(N:ℂ)*∏ p ∈ N.primeFactors, (1-(p:ℂ)⁻¹) := by
  have h := congrArg (fun q : ℚ => (q:ℂ)) (Nat.totient_eq_mul_prod_factors N)
  push_cast at h
  exact h

theorem gamma0Eisenstein_level_factor_normalized (N : ℕ) (hN : 0<N) (s : ℂ) :
    (N.totient:ℂ)*(N:ℂ)^(-2*s)/gamma0EisensteinLevelEulerDenominator N s =
      (N:ℂ)^(1-2*s)*∏ p ∈ N.primeFactors, ((1-(p:ℂ)⁻¹)/(1-(p:ℂ)^(-2*s))) := by
  have hpow : (N:ℂ)^(1-2*s)=(N:ℂ)*(N:ℂ)^(-2*s) := by
    rw [show (1-2*s:ℂ)=1+(-2*s) by ring,
      Complex.cpow_add _ _ (by exact_mod_cast hN.ne'),Complex.cpow_one]
  rw [spectralTotient_complex_product,hpow,Finset.prod_div_distrib]
  unfold gamma0EisensteinLevelEulerDenominator
  ring

theorem gamma0EisensteinTotientSeries_euler_factors (N : ℕ) (hN : 0<N) (s : ℂ) (hs : 1<s.re) :
    gamma0EisensteinTotientSeries N s = (riemannZeta (2*s-1)/riemannZeta (2*s))*
      (N:ℂ)^(1-2*s)*∏ p ∈ N.primeFactors, ((1-(p:ℂ)⁻¹)/(1-(p:ℂ)^(-2*s))) := by
  rw [gamma0EisensteinTotientSeries_level N hN s hs,
    gamma0Eisenstein_level_factor_normalized N hN s]
  ring

end ArtinMatthews
