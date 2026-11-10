module

public import ArtinMatthews.SpectralMacdonaldReciprocal
public import ArtinMatthews.SpectralWeylDimensionlessKernel
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

/-! The evaluated Gaussian-modulus Weyl kernel acts on the actual K
function by an explicit Macdonald multiplier. The stated order of the
iterated integrals is retained. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralWeylGaussian_K_factor {x z p : ℝ} (hx : 0 < x) (hz : 0 < z) (hp : 0 < p)
    (s t r : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) :
    ((∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z : ℝ) : ℂ)*
      schlafliBesselK ((r : ℂ)*Complex.I) z/(z : ℂ) =
        ((Real.sqrt (Real.pi/p) : ℂ)*Complex.exp ((-(s*t)/(8*p) : ℝ) : ℂ))*
          spectralMacdonaldReciprocalIntegrand x (1/(8*p)) r z := by
  rw [spectralWeylDimensionlessKernel_gaussian_signs hx hz hp s t hs ht,Complex.ofReal_mul,Complex.ofReal_exp]
  have he : ((-4*p*x*z-(x/z+z/x+2*s*t)/(16*p) : ℝ) : ℂ) =
      ((-(s*t)/(8*p) : ℝ) : ℂ)+
        (-(((x : ℂ)^2+((1/(8*p) : ℝ) : ℂ)^2)/(2*(x : ℂ)*((1/(8*p) : ℝ) : ℂ)))*(z : ℂ)-
          ((x*(1/(8*p)) : ℝ) : ℂ)/(2*(z : ℂ))) := by
    push_cast
    have hpC : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hzC : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
    field_simp [hpC,hxC,hzC]; ring
  rw [he,Complex.exp_add]
  unfold spectralMacdonaldReciprocalIntegrand
  ring

theorem spectralWeylGaussian_K_integrable {x p : ℝ} (hx : 0 < x) (hp : 0 < p)
    (s t r : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) :
    IntegrableOn (fun z : ℝ =>
      ((∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z : ℝ) : ℂ)*
        schlafliBesselK ((r : ℂ)*Complex.I) z/(z : ℂ)) (Ioi (0 : ℝ)) := by
  have hi := (spectralMacdonaldReciprocalIntegrand_integrable hx (one_div_pos.mpr (by positivity : (0 : ℝ) < 8*p)) r).const_mul
    ((Real.sqrt (Real.pi/p) : ℂ)*Complex.exp ((-(s*t)/(8*p) : ℝ) : ℂ))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact (spectralWeylGaussian_K_factor hx hz hp s t r hs ht).symm

theorem spectralWeylGaussian_K_action {x p : ℝ} (hx : 0 < x) (hp : 0 < p)
    (s t r : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) :
    (∫ z in Ioi (0 : ℝ),
      ((∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z : ℝ) : ℂ)*
        schlafliBesselK ((r : ℂ)*Complex.I) z/(z : ℂ)) =
      2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp ((-(s*t)/(8*p) : ℝ) : ℂ)*
        schlafliBesselK ((r : ℂ)*Complex.I) x*schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)) := by
  have he : (∫ z in Ioi (0 : ℝ),
      ((∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z : ℝ) : ℂ)*
        schlafliBesselK ((r : ℂ)*Complex.I) z/(z : ℂ)) =
      ((Real.sqrt (Real.pi/p) : ℂ)*Complex.exp ((-(s*t)/(8*p) : ℝ) : ℂ))*
        (∫ z in Ioi (0 : ℝ), spectralMacdonaldReciprocalIntegrand x (1/(8*p)) r z) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact spectralWeylGaussian_K_factor hx hz hp s t r hs ht
  rw [he,schlafliBesselK_imaginary_reciprocal_product hx (one_div_pos.mpr (by positivity : (0 : ℝ) < 8*p))]
  ring

end ArtinMatthews
