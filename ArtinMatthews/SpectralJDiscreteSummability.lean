module

public import ArtinMatthews.SpectralJOddCoefficients
public import ArtinMatthews.SpectralBesselJCompactOrderIntegral
public import ArtinMatthews.SpectralBesselJSpatialODE
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
public import Mathlib.Order.CompletePartialOrder
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

/-! Absolute summability and the integrated adjacent-order recurrence for the
actual compact-test Bessel coefficients. -/
noncomputable section
open Set MeasureTheory Complex

namespace ArtinMatthews

theorem spectralJDiscreteCoefficient_summable_norm (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    Summable (fun n : ℕ => ‖spectralJDiscreteCoefficient f n‖) := by
  obtain ⟨C,A,hC,hA,hcoeff⟩ := spectralJDiscreteCoefficient_factorial_bound f hf hc hp
  have hs : Summable (fun n : ℕ => C*(A^n/(n.factorial : ℝ))) :=
    (NormedSpace.expSeries_div_hasSum_exp A).summable.mul_left C
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro n
  simpa only [mul_div_assoc] using hcoeff n

theorem spectralJDiscreteCoefficient_mul_x (f : ℝ → ℂ) (n : ℕ) :
    spectralJDiscreteCoefficient (fun x => (x : ℂ)*f x) n =
      ∫ x in Ioi (0 : ℝ), f x*Complex.besselJ (n : ℂ) (x : ℂ) := by
  unfold spectralJDiscreteCoefficient
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  field_simp [hxC]

theorem spectralJDiscreteCoefficient_adjacent (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (n : ℕ) :
    (2 : ℂ)*((n+1 : ℕ) : ℂ)*spectralJDiscreteCoefficient f (n+1) =
      spectralJDiscreteCoefficient (fun x => (x : ℂ)*f x) n +
        spectralJDiscreteCoefficient (fun x => (x : ℂ)*f x) (n+2) := by
  let g : ℝ → ℂ := fun x => (x : ℂ)*f x
  have hg : Continuous g := Complex.continuous_ofReal.mul hf
  have hgc : HasCompactSupport g := hc.mul_left
  have hgp : tsupport g ⊆ Ioi (0 : ℝ) := tsupport_mul_subset_right.trans hp
  have hi (j : ℕ) : IntegrableOn (fun x => f x*Complex.besselJ (j : ℂ) (x : ℂ))
      (Ioi (0 : ℝ)) := by
    have h := spectralBesselJOrderTransform_integrable g hg hgc hgp (j : ℂ)
    apply h.congr_fun _ measurableSet_Ioi
    intro x hx
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    dsimp [g]
    field_simp [hxC]
  rw [spectralJDiscreteCoefficient_mul_x,spectralJDiscreteCoefficient_mul_x,
    ← integral_add (hi n) (hi (n+2))]
  unfold spectralJDiscreteCoefficient
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have h := spectral_besselJ_order_recurrence (n : ℂ) hx
  push_cast at h ⊢
  field_simp [hxC] at h ⊢
  linear_combination -(f x)*h

end ArtinMatthews
