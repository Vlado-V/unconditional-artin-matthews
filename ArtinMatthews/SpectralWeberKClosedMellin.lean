module

public import ArtinMatthews.SpectralWeberKClosed
public import ArtinMatthews.SpectralAntiKMellinEvaluation
public import ArtinMatthews.SpectralWeberKScalar
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

/-! The explicit Weber expression has the same actual Mellin transform
as the Gaussian K integral; every constant is evaluated here. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralWeberKClosed_mellin (ν s : ℂ) (hs : 0 < s.re)
    (hstrip : s.re+|ν.re| < 1/2) :
    mellin (spectralWeberKClosed ν) s =
      Complex.Gamma s*(2 : ℂ)^(-1-2*s)*Complex.Gamma (1/2-s-ν)*
        Complex.Gamma (1/2-s+ν) := by
  have hleft : |ν.re| < ((1/2 : ℂ)-s).re := by norm_num; linarith
  have hright : ((1/2 : ℂ)-s).re < 1/2 := by norm_num; linarith
  rw [spectralWeberKClosed_mellin_scale,
    (spectralAntiK_hasMellin ν (1/2-s) hleft hright).2,
    show ((1/2 : ℂ)-s)+1/2 = 1-s by ring]
  calc
    _ = (((Real.sqrt Real.pi : ℂ)/(4*Complex.cos ((Real.pi : ℂ)*ν)))*
        (1/8 : ℂ)^(s-1/2)*
        ((Real.sqrt Real.pi : ℂ)*(2 : ℂ)^(-(1/2-s))*Complex.cos ((Real.pi : ℂ)*ν)/
          (Complex.Gamma (1-s)*Complex.cos ((Real.pi : ℂ)*(1/2-s)))))*
        Complex.Gamma (1/2-s-ν)*Complex.Gamma (1/2-s+ν) := by ring
    _ = _ := by rw [spectralWeberK_scalar ν s hs hstrip]

end ArtinMatthews
