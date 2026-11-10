module

public import ArtinMatthews.SpectralJForwardWeylNormalization
public import ArtinMatthews.SpectralJForwardHolomorphic
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! Exact complex linearity in the original compact positive test. -/
noncomputable section
open Set MeasureTheory Complex

namespace ArtinMatthews

theorem spectralJForwardTransform_const_mul (a : ℂ) (f : ℝ → ℂ) (z : ℂ) :
    spectralJForwardTransform (fun x => a*f x) z = a*spectralJForwardTransform f z := by
  unfold spectralJForwardTransform
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change a*f x*spectralJForwardKernel z x/(x : ℂ) =
    a*(f x*spectralJForwardKernel z x/(x : ℂ))
  ring

theorem spectralJForwardTransform_add (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfp : tsupport f ⊆ Ioi (0 : ℝ)) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) (z : ℂ) :
    spectralJForwardTransform (f+g) z = spectralJForwardTransform f z + spectralJForwardTransform g z := by
  have hA : spectralBesselJOrderTransform (f+g) = spectralBesselJOrderTransform f + spectralBesselJOrderTransform g := by
    funext ν
    unfold spectralBesselJOrderTransform
    change (∫ x in Ioi (0 : ℝ), (f x+g x)*Complex.besselJ ν (x : ℂ)/(x : ℂ)) =
      (∫ x in Ioi (0 : ℝ), f x*Complex.besselJ ν (x : ℂ)/(x : ℂ)) +
        (∫ x in Ioi (0 : ℝ), g x*Complex.besselJ ν (x : ℂ)/(x : ℂ))
    rw [← integral_add (spectralBesselJOrderTransform_integrable f hf hfc hfp ν)
      (spectralBesselJOrderTransform_integrable g hg hgc hgp ν)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change (f x+g x)*Complex.besselJ ν (x : ℂ)/(x : ℂ) =
      f x*Complex.besselJ ν (x : ℂ)/(x : ℂ) + g x*Complex.besselJ ν (x : ℂ)/(x : ℂ)
    ring
  have hfgp : tsupport (f+g) ⊆ Ioi (0 : ℝ) := (tsupport_add f g).trans (union_subset hfp hgp)
  rw [spectralJForwardTransform_eq_divided_order (f+g) (hf.add hg) (hfc.add hgc) hfgp z,
    spectralJForwardTransform_eq_divided_order f hf hfc hfp z,
    spectralJForwardTransform_eq_divided_order g hg hgc hgp z,hA]
  by_cases hz : z = 0
  · subst z
    simp only [ite_true]
    rw [deriv_add (spectralBesselJOrderTransform_differentiable f hf hfc hfp 0)
      (spectralBesselJOrderTransform_differentiable g hg hgc hgp 0)]
    ring
  · simp only [ite_eq_right hz, Pi.add_apply]
    ring

theorem spectralJForwardSpectralWeight_const_mul (a : ℂ) (f : ℝ → ℂ) (z : ℂ) :
    spectralJForwardSpectralWeight (fun x => a*f x) z = a*spectralJForwardSpectralWeight f z := by
  rw [spectralJForwardSpectralWeight,spectralJForwardSpectralWeight,
    spectralJForwardTransform_const_mul]
  ring

theorem spectralJForwardSpectralWeight_add (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfp : tsupport f ⊆ Ioi (0 : ℝ)) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) (z : ℂ) :
    spectralJForwardSpectralWeight (f+g) z = spectralJForwardSpectralWeight f z + spectralJForwardSpectralWeight g z := by
  rw [spectralJForwardSpectralWeight,spectralJForwardSpectralWeight,spectralJForwardSpectralWeight,
    spectralJForwardTransform_add f g hf hg hfc hgc hfp hgp]
  ring

end ArtinMatthews
