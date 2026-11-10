module

public import ArtinMatthews.SpectralQuadraticFourierReduction
public import ArtinMatthews.SpectralCuspFourierODEHorizontal
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
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! The actual one-dimensional quadratic Fourier integral is evaluated
through the proved two-dimensional Schlaefli kernel and absolute Fubini. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralRealFourierPhase_int (n : ℤ) (x : ℝ) :
    spectralRealFourierPhase (n : ℝ) x = cuspFourierPhase 1 n x := by
  unfold spectralRealFourierPhase cuspFourierPhase cuspFourierFrequency
  congr 1
  push_cast
  ring

theorem spectralQuadraticFourier_bessel (s : ℂ) (hs : 1/2 < s.re) (b : ℝ) (hb : b ≠ 0) :
    spectralQuadraticFourier s b =
      ((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s) *
        ((Real.pi*|b| : ℝ) : ℂ)^(s-1/2) *
          schlafliBesselK (s-1/2) (2*Real.pi*|b|) := by
  have hS : 1 < (s+(1/2 : ℂ)).re := by
    simp only [Complex.add_re]
    norm_num
    linarith
  have hbC : (((b/2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast div_ne_zero hb (by norm_num : (2 : ℝ) ≠ 0)
  have hn : ‖((b/2 : ℝ) : ℂ)‖ = |b|/2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  have hKernel := sourceFourierKernel_bessel (s+1/2) ((b/2 : ℝ) : ℂ) hS hbC
  rw [hn,show s+(1/2 : ℂ)-1=s-1/2 by ring,
    show (2 : ℂ)*(Real.pi : ℂ)*((|b|/2 : ℝ) : ℂ) =
      ((Real.pi*|b| : ℝ) : ℂ) by push_cast;ring,
    show 4*Real.pi*(|b|/2)=2*Real.pi*|b| by ring] at hKernel
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hGS : Complex.Gamma (s+1/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hsq : (Real.sqrt Real.pi : ℂ)^2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hroot : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  let C : ℂ := (Real.sqrt Real.pi : ℂ)*Complex.Gamma s/Complex.Gamma (s+1/2)
  have hC : C ≠ 0 := div_ne_zero (mul_ne_zero hroot hG) hGS
  have hScalar : C*((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s) =
      (2*Real.pi : ℂ)/Complex.Gamma (s+1/2) := by
    dsimp only [C]
    calc
      _ = (2*(Real.sqrt Real.pi : ℂ)^2/Complex.Gamma (s+1/2)) *
          (Complex.Gamma s/Complex.Gamma s) := by ring
      _ = _ := by rw [div_self hG,mul_one,hsq]
  apply mul_left_cancel₀ hC
  calc
    C*spectralQuadraticFourier s b = sourceFourierKernel (s+1/2) ((b/2 : ℝ) : ℂ) :=
      spectralQuadraticFourier_dimensional_reduction s hs b
    _ = _ := hKernel
    _ = C*(((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s) *
        ((Real.pi*|b| : ℝ) : ℂ)^(s-1/2)*schlafliBesselK (s-1/2) (2*Real.pi*|b|)) := by
      rw [show C*(((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s) *
          ((Real.pi*|b| : ℝ) : ℂ)^(s-1/2)*schlafliBesselK (s-1/2) (2*Real.pi*|b|)) =
          (C*((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s)) *
            ((Real.pi*|b| : ℝ) : ℂ)^(s-1/2)*schlafliBesselK (s-1/2) (2*Real.pi*|b|) by ring,
        hScalar]

end ArtinMatthews

