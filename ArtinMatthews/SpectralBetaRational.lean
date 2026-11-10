module

public import ArtinMatthews.SpectralBetaLogistic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine beta integral in positive rational coordinates. -/
noncomputable section
open Set MeasureTheory
namespace ArtinMatthews

def spectralBetaRationalProfile (a b : ℂ) (t : ℝ) : ℂ :=
  (t:ℂ)^(a-1)*(1+(t:ℂ))^(-a-b)

theorem spectralBetaRationalProfile_exp_jacobian (a b : ℂ) (u : ℝ) :
    Real.exp u • spectralBetaRationalProfile a b (Real.exp u) =
      spectralBetaLogProfile a b u := by
  have he : (Real.exp u:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'
  have hB : 0<1+Real.exp u := by positivity
  have hBc : (1+(Real.exp u:ℂ))≠0 := by exact_mod_cast hB.ne'
  have hsig : Real.sigmoid u=Real.exp u/(1+Real.exp u) := by
    rw [Real.sigmoid_def,Real.exp_neg]
    field_simp [(Real.exp_pos u).ne']
    ring
  have hsigc : 1-Real.sigmoid u=1/(1+Real.exp u) := by rw [hsig]; field_simp; ring
  unfold spectralBetaRationalProfile spectralBetaLogProfile
  rw [Complex.real_smul,hsigc,hsig,Complex.ofReal_div,Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg (Real.exp_pos u).le hB.le,
    Complex.div_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤1) hB.le,
    Complex.ofReal_add,Complex.ofReal_one,Complex.one_cpow,Complex.cpow_sub _ _ he,
    Complex.cpow_one]
  rw [show -a-b=-(a+b) by ring,Complex.cpow_neg,Complex.cpow_add _ _ hBc]
  field_simp

theorem spectralBetaRationalProfile_integrable (a b : ℂ) (ha : 0<a.re) (hb : 0<b.re) :
    IntegrableOn (spectralBetaRationalProfile a b) (Ioi 0) := by
  rw [← integrable_comp_exp]
  simpa only [spectralBetaRationalProfile_exp_jacobian] using
    spectralBetaLogProfile_integrable a b ha hb

theorem spectralBetaRationalProfile_integral (a b : ℂ) :
    (∫ t : ℝ in Ioi 0, spectralBetaRationalProfile a b t) = Complex.betaIntegral a b := by
  rw [← integral_comp_exp]
  simpa only [spectralBetaRationalProfile_exp_jacobian] using spectralBetaLogProfile_integral a b

end ArtinMatthews
