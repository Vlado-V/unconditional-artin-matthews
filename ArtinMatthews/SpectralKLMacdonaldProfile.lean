module

public import ArtinMatthews.SpectralKLExpReciprocal
public import ArtinMatthews.SpectralMacdonaldReciprocal
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

/-! The actual noncompact physical profile produced by Gaussian Weyl
integration, with its literal K analysis integral. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralKLMacdonaldProfile (x y : ℝ) : ℝ → ℂ :=
  spectralKLExpReciprocal ((x^2+y^2)/(2*x*y)) (x*y/2)

theorem spectralKLMacdonaldProfile_memLp {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    MemLp (spectralKLMacdonaldProfile x y) 2 spectralKLPhysicalMeasure := by
  apply spectralKLExpReciprocal_memLp
  · exact div_pos (by positivity) (by positivity)
  · positivity

theorem spectralKLMacdonaldProfile_kernel {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (t : ℝ) :
    schlafliBesselK ((t : ℂ)*Complex.I) z*spectralKLMacdonaldProfile x y z/(z : ℂ) =
      spectralMacdonaldReciprocalIntegrand x y t z := by
  unfold spectralKLMacdonaldProfile spectralKLExpReciprocal spectralMacdonaldReciprocalIntegrand
  rw [ite_eq_left hz]
  have he : -((((x^2+y^2)/(2*x*y) : ℝ) : ℂ))*(z : ℂ)-(((x*y/2 : ℝ) : ℂ))/(z : ℂ) =
      -(((x : ℂ)^2+(y : ℂ)^2)/(2*x*y))*(z : ℂ)-((x*y : ℝ) : ℂ)/(2*z) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hx.ne',Complex.ofReal_ne_zero.mpr hy.ne',
      Complex.ofReal_ne_zero.mpr hz.ne']
  rw [he]
  ring

theorem spectralKLMacdonaldProfile_kernel_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    IntegrableOn (fun z : ℝ => schlafliBesselK ((t : ℂ)*Complex.I) z*
      spectralKLMacdonaldProfile x y z/(z : ℂ)) (Ioi (0 : ℝ)) := by
  apply (spectralMacdonaldReciprocalIntegrand_integrable hx hy t).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact (spectralKLMacdonaldProfile_kernel hx hy hz t).symm

theorem spectralKLMacdonaldProfile_analysis_integral {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    (∫ z in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) z*
      spectralKLMacdonaldProfile x y z/(z : ℂ)) =
      2*schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((t : ℂ)*Complex.I) y := by
  calc
    _ = ∫ z in Ioi (0 : ℝ), spectralMacdonaldReciprocalIntegrand x y t z := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z hz
      exact spectralKLMacdonaldProfile_kernel hx hy hz t
    _ = _ := schlafliBesselK_imaginary_reciprocal_product hx hy t

end ArtinMatthews
