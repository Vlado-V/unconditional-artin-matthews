module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralAntiKBetaGamma
public import ArtinMatthews.SpectralAntiKMellin
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! Closed Gamma evaluation of the actual growing-exponential K Mellin
integral, with the natural upper boundary Re(s)<1/2. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralAntiK_mellin (ν s : ℂ) (hs : |ν.re| < s.re) (hsh : s.re < 1/2) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*Complex.exp (x : ℂ)*schlafliBesselK ν x) =
      (Real.sqrt Real.pi : ℂ)*(2 : ℂ)^(-s)*Complex.Gamma (s+ν)*Complex.Gamma (s-ν)*
        Complex.cos ((Real.pi : ℂ)*ν)/
        (Complex.Gamma (s+1/2)*Complex.cos ((Real.pi : ℂ)*s)) := by
  rw [spectralAntiK_mellin_beta ν s hs hsh,spectralAntiK_beta_gamma ν s hs hsh]

theorem spectralAntiK_hasMellin (ν s : ℂ) (hs : |ν.re| < s.re) (hsh : s.re < 1/2) :
    HasMellin (fun x : ℝ => Complex.exp (x : ℂ)*schlafliBesselK ν x) s
      ((Real.sqrt Real.pi : ℂ)*(2 : ℂ)^(-s)*Complex.Gamma (s+ν)*Complex.Gamma (s-ν)*
        Complex.cos ((Real.pi : ℂ)*ν)/
        (Complex.Gamma (s+1/2)*Complex.cos ((Real.pi : ℂ)*s))) := by
  constructor
  · simpa only [MellinConvergent,smul_eq_mul,mul_assoc] using
      spectralAntiK_mellin_integrable ν s hs hsh
  · simpa only [mellin,smul_eq_mul,mul_assoc] using spectralAntiK_mellin ν s hs hsh

end ArtinMatthews
