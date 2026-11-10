module

public import ArtinMatthews.SpectralWeylDimensionlessKernel
public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralWeberKBasic
public import ArtinMatthews.SpectralWeberKNormalization
public import ArtinMatthews.SpectralWeylGaussianKAction
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact opposite-sign K multiplier under Gaussian modulus testing.
The geometric side keeps the already proved modulus-first integration order. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralWeylKMultiplier_gaussian_integrable (r : ℝ) {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun X : ℝ => Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (8*(Real.cosh (Real.pi*r) : ℂ)*schlafliBesselK (2*((r : ℂ)*Complex.I)) X/(X : ℂ)))
      (Ioi (0 : ℝ)) := by
  have hν : |((r : ℂ)*Complex.I).re| < 1/2 := by norm_num
  have hi := (spectralWeberK_integrable hν hp).const_mul (8*(Real.cosh (Real.pi*r) : ℂ))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  field_simp [Complex.ofReal_ne_zero.mpr hX.ne']

theorem spectralWeylKMultiplier_gaussian (r : ℝ) {p : ℝ} (hp : 0 < p) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (8*(Real.cosh (Real.pi*r) : ℂ)*schlafliBesselK (2*((r : ℂ)*Complex.I)) X/(X : ℂ))) =
      2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp ((1/(8*p) : ℝ) : ℂ)*
        schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)) := by
  have he : (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (8*(Real.cosh (Real.pi*r) : ℂ)*schlafliBesselK (2*((r : ℂ)*Complex.I)) X/(X : ℂ))) =
      (8*(Real.cosh (Real.pi*r) : ℂ))*
        (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*
          schlafliBesselK (2*((r : ℂ)*Complex.I)) X) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro X hX
    dsimp only
    field_simp [Complex.ofReal_ne_zero.mpr hX.ne']
  rw [he,schlafliBesselK_imaginary_gaussian_weber r hp]
  have hc : (Real.cosh (Real.pi*r) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    have h := Real.one_le_cosh (Real.pi*r)
    linarith
  field_simp [hc]
  ring_nf

theorem spectralWeylGaussian_opposite_K_multiplier {x p : ℝ} (hx : 0 < x) (hp : 0 < p)
    (s t r : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = -1) :
    (∫ z in Ioi (0 : ℝ),
      ((∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z : ℝ) : ℂ)*
        schlafliBesselK ((r : ℂ)*Complex.I) z/(z : ℂ)) =
      schlafliBesselK ((r : ℂ)*Complex.I) x*
        (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
          (8*(Real.cosh (Real.pi*r) : ℂ)*schlafliBesselK (2*((r : ℂ)*Complex.I)) X/(X : ℂ))) := by
  rw [spectralWeylGaussian_K_action hx hp s t r hs ht,spectralWeylKMultiplier_gaussian r hp,hst]
  norm_num only [neg_neg,one_div]
  ring

end ArtinMatthews
