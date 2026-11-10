module

public import ArtinMatthews.SpectralCuspBesselTransform
public import ArtinMatthews.SpectralCuspEisensteinFourierDirichlet
public import ArtinMatthews.SpectralEisensteinFourierCompact
public import ArtinMatthews.SpectralCuspEisensteinFourierBessel
public import ArtinMatthews.SpectralEisensteinFourierInitial
public import ArtinMatthews.SpectralQuadraticFourierBessel
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

/-! The actual completed Eisenstein Fourier coefficient is calibrated with
its evaluated K-Bessel and true-width Dirichlet formula on Re(s)>1. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0CuspInitialFourierAmplitude (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (n : ℤ) (s : ℂ) : ℂ :=
  ((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s)*
    ((Real.pi*|(n : ℝ)| : ℝ) : ℂ)^(s-1/2)*gamma0CuspFourierDirichlet N r a n s

theorem gamma0UnitCuspFourierMean_initial_bessel (N : ℕ) [NeZero N]
    (r a : SL(2, ℤ)) (s : ℂ) (hs : 1 < s.re) (n : ℤ) (hn : n ≠ 0)
    (y : ℝ) (hy : 0 < y) :
    gamma0UnitCuspFourierMean N r n (gamma0CuspEisenstein N a s) y =
      gamma0CuspInitialFourierAmplitude N r a n s*
        cuspBesselKernel (s-1/2) (2*Real.pi*|(n : ℝ)|) y := by
  rw [gamma0UnitCuspFourierMean,dite_eq_left hy]
  have h := gamma0CuspEisenstein_nonzero_fourier_bessel N r a s hs n hn y hy
  calc
    _ = ∫ x in (0 : ℝ)..1,gamma0CuspEisenstein N a s
        (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x)*
          spectralRealFourierPhase (n : ℝ) x := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [spectralRealFourierPhase_int]
      exact mul_comm _ _
    _ = _ := by rw [h]; unfold gamma0CuspInitialFourierAmplitude; ring

theorem gamma0CuspEisensteinFourierCoefficient_initial_bessel_ae (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (s : ℂ) (hs : 1 < s.re) :
    gamma0CuspEisensteinFourierCoefficient N a r Y hY n s =ᵐ[volume.restrict (Ioi Y)]
      fun y => gamma0CuspInitialFourierAmplitude N r a n s*
        cuspBesselKernel (s-1/2) (2*Real.pi*|(n : ℝ)|)
          (y/(gamma0CuspTrueWidth N r : ℝ)) := by
  filter_upwards [gamma0CuspEisensteinFourierCoefficient_initial_ae N a r Y hY n s hs,
    ae_restrict_mem measurableSet_Ioi] with y hy hyY
  rw [hy,gamma0UnitCuspFourierMean_initial_bessel N r a s hs n hn]
  exact div_pos (hY.trans hyY) (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r))

end ArtinMatthews
