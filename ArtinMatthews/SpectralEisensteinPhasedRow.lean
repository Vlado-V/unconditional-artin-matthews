module

public import ArtinMatthews.SpectralEisensteinHorizontalBessel
public import ArtinMatthews.SpectralEisensteinRowKernel
public import ArtinMatthews.SpectralCuspTwoCellFourier
public import ArtinMatthews.SpectralIntegerPeriodUnfolding
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual integer-translate positive-row orbit with its nonzero
horizontal Fourier phase. Absolute integrability precedes unfolding. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectralRealFourierPhase_add (b x y : ℝ) :
    spectralRealFourierPhase b (x+y) =
      spectralRealFourierPhase b x*spectralRealFourierPhase b y := by
  unfold spectralRealFourierPhase
  have h : -((2*Real.pi*b*(x+y) : ℝ) : ℂ)*Complex.I =
      -((2*Real.pi*b*x : ℝ) : ℂ)*Complex.I + -((2*Real.pi*b*y : ℝ) : ℂ)*Complex.I := by
    push_cast
    ring
  rw [h,Complex.exp_add]

theorem spectralRealFourierPhase_integer_add (n k : ℤ) (x : ℝ) :
    spectralRealFourierPhase (n : ℝ) (x+(k : ℝ)) = spectralRealFourierPhase (n : ℝ) x := by
  simp only [spectralRealFourierPhase_int]
  simpa only [mul_one] using (cuspFourierPhase_periodic 1 one_pos n).int_mul k x

theorem eisensteinHorizontalShiftedFourier_integrable (s : ℂ) (hs : 1/2 < s.re)
    (b y a : ℝ) (hy : 0 < y) :
    Integrable (fun x => eisensteinHorizontalKernel s y x*spectralRealFourierPhase b (x-a)) := by
  apply (eisensteinHorizontalKernel_integrable s hs y hy).norm.mono'
  · unfold eisensteinHorizontalKernel spectralRealFourierPhase
    fun_prop
  · exact ae_of_all _ fun x => by rw [norm_mul,spectralRealFourierPhase_norm,mul_one]

theorem eisensteinRealRowTerm_phased_orbit (s : ℂ) (hs : 1/2 < s.re)
    (c a y : ℝ) (hc : 0 < c) (hy : 0 < y) (n : ℤ) :
    (∑' k : ℤ, ∫ x in (0 : ℝ)..1,
      eisensteinRealRowTerm s c (a+c*(k : ℝ)) x y*spectralRealFourierPhase (n : ℝ) x) =
      (c : ℂ)^(-2*s)*spectralRealFourierPhase (n : ℝ) (-a/c)*
        eisensteinHorizontalFourier s (n : ℝ) y := by
  let d : ℝ := a/c
  let F (x : ℝ) := eisensteinHorizontalKernel s y x*spectralRealFourierPhase (n : ℝ) (x-d)
  have hF : Integrable F := eisensteinHorizontalShiftedFourier_integrable s hs (n : ℝ) y d hy
  have hp (k : ℤ) (x : ℝ) :
      eisensteinRealRowTerm s c (a+c*(k : ℝ)) x y*spectralRealFourierPhase (n : ℝ) x =
        (c : ℂ)^(-2*s)*F (x+(k : ℝ)+d) := by
    rw [eisensteinRealRowTerm_translate s c hc a x y hy k]
    dsimp only [F,d]
    rw [add_sub_cancel_right,spectralRealFourierPhase_integer_add]
    ring
  simp_rw [hp,intervalIntegral.integral_const_mul]
  rw [tsum_mul_left,spectralIntegerPeriodUnfolding_shift F hF d]
  have hF' : F = fun x => spectralRealFourierPhase (n : ℝ) (-d)*
      (eisensteinHorizontalKernel s y x*spectralRealFourierPhase (n : ℝ) x) := by
    funext x
    dsimp only [F]
    rw [sub_eq_add_neg,spectralRealFourierPhase_add]
    ring
  rw [hF',integral_const_mul]
  change (c : ℂ)^(-2*s)*(spectralRealFourierPhase (n : ℝ) (-d)*
    eisensteinHorizontalFourier s (n : ℝ) y) = _
  rw [show -d = -a/c by dsimp [d];ring]
  ring

theorem eisensteinRealRowTerm_phased_orbit_bessel (s : ℂ) (hs : 1/2 < s.re)
    (c a y : ℝ) (hc : 0 < c) (hy : 0 < y) (n : ℤ) (hn : n ≠ 0) :
    (∑' k : ℤ, ∫ x in (0 : ℝ)..1,
      eisensteinRealRowTerm s c (a+c*(k : ℝ)) x y*spectralRealFourierPhase (n : ℝ) x) =
      (c : ℂ)^(-2*s)*spectralRealFourierPhase (n : ℝ) (-a/c)*
        (((2*(Real.sqrt Real.pi : ℂ))/Complex.Gamma s) *
          ((Real.pi*|(n : ℝ)| : ℝ) : ℂ)^(s-1/2)*
            cuspBesselKernel (s-1/2) (2*Real.pi*|(n : ℝ)|) y) := by
  rw [eisensteinRealRowTerm_phased_orbit s hs c a y hc hy n,
    eisensteinHorizontalFourier_bessel s hs (n : ℝ) y (by exact_mod_cast hn) hy]

end ArtinMatthews

