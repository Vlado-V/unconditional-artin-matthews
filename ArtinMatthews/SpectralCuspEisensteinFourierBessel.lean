module

public import ArtinMatthews.SpectralCuspBesselTransform
public import ArtinMatthews.SpectralCuspEisensteinFourierDirichlet
public import ArtinMatthews.SpectralCuspEisensteinSeries
public import ArtinMatthews.SpectralGamma0EisensteinIntegralExchange
public import ArtinMatthews.SpectralQuadraticFourierReduction
public import ArtinMatthews.SpectralCuspEisensteinFourierPositive
public import ArtinMatthews.SpectralCuspEisensteinFourierSigns
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

/-! The actual nonzero Fourier coefficient of the convergent all-cusp
Eisenstein series, with the genuine true-width Kloosterman Dirichlet
series and the evaluated K-Bessel kernel. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0CuspEisenstein_nonzero_fourier_bessel (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (hs : 1 < s.re) (n : ℤ) (hn : n ≠ 0)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,gamma0CuspEisenstein N a s
      (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x)*
        spectralRealFourierPhase (n : ℝ) x) =
      ((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s) *
        ((Real.pi*|(n : ℝ)| : ℝ) : ℂ)^(s-1/2) *
          cuspBesselKernel (s-1/2) (2*Real.pi*|(n : ℝ)|) y *
            gamma0CuspFourierDirichlet N r a n s := by
  rw [gamma0CuspEisenstein_nonzero_fourier_positive_rows N r a s hs n hn y hy,
    cuspEisensteinPositiveFourier_dirichlet N r a s hs n y hy,
    eisensteinHorizontalFourier_bessel s (by linarith) (n : ℝ) y (by exact_mod_cast hn) hy,
    gamma0CuspFourierDirichlet_normalized]
  ring

end ArtinMatthews

