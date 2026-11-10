module

public import ArtinMatthews.SpectralKLInverseIEnvelope
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex OAI.CubicEisenstein
open scoped ComplexConjugate
noncomputable section

theorem spectralKLCompactOrderTransform_real_line (g : ℝ → ℂ)
    (hp : tsupport g ⊆ Ioi (0 : ℝ)) (hg : ∀ x : ℝ, star (g x) = g x) (t : ℝ) :
    star (spectralKLCompactOrderTransform g ((t : ℂ) * I)) =
      spectralKLCompactOrderTransform g ((t : ℂ) * I) := by
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
    change conj (r : ℂ) = (r : ℂ)
    exact conj_ofReal r
  change conj _ = _
  unfold spectralKLCompactOrderTransform
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : 0 < x
  · rw [spectralKLCompactOrderIntegrand, schlafliBesselK_imaginary_eq_realKernel t hx,
      spectralKLPhysicalCompactDiv]
    simpa only [map_mul, map_div₀, conj_ofReal, starRingEnd_apply, hreal] using congrArg
      (fun z : ℂ => (spectralKLRealKernel t x : ℂ) * (z / (x : ℂ))) (hg x)
  · have h0 : g x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hp hh))
    simp [spectralKLCompactOrderIntegrand, spectralKLPhysicalCompactDiv, h0]

theorem spectralKLWindowData_real (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hp : tsupport g ⊆ Ioi (0 : ℝ)) (hg : ∀ x : ℝ, star (g x) = g x)
    (hh : ∀ t : ℝ, star (h (t : ℂ)) = h (t : ℂ)) (t : ℝ) :
    star (spectralKLWindowData h g t) = spectralKLWindowData h g t := by
  rw [spectralKLWindowData, star_mul', hh t, spectralKLCompactOrderTransform_real_line g hp hg t]

theorem spectralKLWindowSynthesis_real (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hp : tsupport g ⊆ Ioi (0 : ℝ)) (hg : ∀ x : ℝ, star (g x) = g x)
    (hh : ∀ t : ℝ, star (h (t : ℂ)) = h (t : ℂ)) (x : ℝ) :
    star (spectralKLWindowSynthesis h g x) = spectralKLWindowSynthesis h g x := by
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
    change conj (r : ℂ) = (r : ℂ)
    exact conj_ofReal r
  rw [spectralKLWindowSynthesis]
  by_cases hx : 0 < x
  · rw [ite_eq_left hx, spectralKLWeightedSynthesis]
    change conj _ = _
    rw [← integral_conj]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [schlafliBesselK_imaginary_eq_realKernel t hx]
    simpa only [map_mul, conj_ofReal, starRingEnd_apply, hreal] using congrArg
      (fun z : ℂ => (spectralKLRealKernel t x : ℂ) * z * (spectralKLPlancherelWeight t : ℂ))
      (spectralKLWindowData_real h g hp hg hh t)
  · simp only [ite_eq_right hx, star_zero]

theorem spectralKLWindowSynthesis_ofReal_re (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hp : tsupport g ⊆ Ioi (0 : ℝ)) (hg : ∀ x : ℝ, star (g x) = g x)
    (hh : ∀ t : ℝ, star (h (t : ℂ)) = h (t : ℂ)) (x : ℝ) :
    ((spectralKLWindowSynthesis h g x).re : ℂ) = spectralKLWindowSynthesis h g x := by
  have heq := congrArg Complex.im (spectralKLWindowSynthesis_real h g hp hg hh x)
  change -(spectralKLWindowSynthesis h g x).im = (spectralKLWindowSynthesis h g x).im at heq
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

end
end ArtinMatthews
