module

public import ArtinMatthews.SpectralJGaussianTail
public import ArtinMatthews.SpectralJGaussianTailKLBound
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
public import Mathlib.RingTheory.PiTensorProduct
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

/-! The actual tail coefficient is linear under its proved absolute-integrability bounds. -/
namespace ArtinMatthews
open Set Filter MeasureTheory OAI.CubicEisenstein
open scoped BigOperators
noncomputable section

def spectralJRawKLCoefficient (F : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ y : ℝ in Ioi 0, spectralJGaussianTail F y *
    schlafliBesselK ((r : ℂ) * Complex.I) y / (y : ℂ)

private theorem swapped_tail_integrable (F : ℝ → ℂ) (hF : Measurable F)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ w : ℝ, 2 < w → ‖F w‖ ≤ B / w) (r : ℝ) :
    IntegrableOn (fun w : ℝ => F w * ∫ y : ℝ in Ioi 0, spectralJTailKernel r y w) (Ioi 2) := by
  have hi := (spectralJTailKernel_pair_integrable F hF B hB hb r).integral_prod_right
  apply hi.congr
  filter_upwards with w
  change (∫ y : ℝ in Ioi 0, spectralJTailKernel r y w * F w) =
    F w * ∫ y : ℝ in Ioi 0, spectralJTailKernel r y w
  rw [integral_mul_const, mul_comm]

theorem spectralJRawKLCoefficient_const_mul (c : ℂ) (F : ℝ → ℂ) (r : ℝ) :
    spectralJRawKLCoefficient (fun w => c * F w) r = c * spectralJRawKLCoefficient F r := by
  have hrow (y : ℝ) (hy : 0 < y) :
      spectralJGaussianTail (fun w => c * F w) y = c * spectralJGaussianTail F y := by
    have he : (∫ w : ℝ in Ioi 2, (Real.exp (-(y * w)) : ℂ) * (c * F w)) =
        c * ∫ w : ℝ in Ioi 2, (Real.exp (-(y * w)) : ℂ) * F w := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro w _
      dsimp only
      ring
    simp only [spectralJGaussianTail, ite_eq_left hy]
    rw [he, mul_left_comm]
  unfold spectralJRawKLCoefficient
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  rw [hrow y (mem_Ioi.mp hy)]
  ring

theorem spectralJRawKLCoefficient_add (F G : ℝ → ℂ)
    (hF : Measurable F) (hG : Measurable G)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hb : ∀ w : ℝ, 2 < w → ‖F w‖ ≤ B / w) (hd : ∀ w : ℝ, 2 < w → ‖G w‖ ≤ D / w)
    (r : ℝ) :
    spectralJRawKLCoefficient (fun w => F w + G w) r =
      spectralJRawKLCoefficient F r + spectralJRawKLCoefficient G r := by
  have he (w : ℝ) (hw : 2 < w) : ‖F w + G w‖ ≤ (B + D) / w := by
    rw [add_div]
    exact (norm_add_le _ _).trans (add_le_add (hb w hw) (hd w hw))
  change spectralJRawKLCoefficient (F + G) r = _
  unfold spectralJRawKLCoefficient
  rw [spectralJGaussianTail_KLIntegral_eq (F + G) (hF.add hG) (B + D) (add_nonneg hB hD) he r,
    spectralJGaussianTail_KLIntegral_eq F hF B hB hb r,
    spectralJGaussianTail_KLIntegral_eq G hG D hD hd r]
  simp only [Pi.add_apply, add_mul]
  exact integral_add (swapped_tail_integrable F hF B hB hb r)
    (swapped_tail_integrable G hG D hD hd r)

theorem spectralJRawKLCoefficient_finsetSum {ι : Type*} (s : Finset ι)
    (F : ι → ℝ → ℂ) (B : ι → ℝ)
    (hF : ∀ i ∈ s, Measurable (F i)) (hB : ∀ i ∈ s, 0 ≤ B i)
    (hb : ∀ i ∈ s, ∀ w : ℝ, 2 < w → ‖F i w‖ ≤ B i / w) (r : ℝ) :
    spectralJRawKLCoefficient (fun w => ∑ i ∈ s, F i w) r =
      ∑ i ∈ s, spectralJRawKLCoefficient (F i) r := by
  have hm : Measurable (fun w => ∑ i ∈ s, F i w) := s.measurable_fun_sum hF
  have hs : 0 ≤ ∑ i ∈ s, B i := Finset.sum_nonneg hB
  have he (w : ℝ) (hw : 2 < w) : ‖∑ i ∈ s, F i w‖ ≤ (∑ i ∈ s, B i) / w := by
    rw [Finset.sum_div]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => hb i hi w hw))
  let A (w : ℝ) := ∫ y : ℝ in Ioi 0, spectralJTailKernel r y w
  calc
    _ = ∫ w : ℝ in Ioi 2, (∑ i ∈ s, F i w) * A w :=
      spectralJGaussianTail_KLIntegral_eq _ hm _ hs he r
    _ = ∑ i ∈ s, ∫ w : ℝ in Ioi 2, F i w * A w := by
      simp only [Finset.sum_mul]
      exact integral_finsetSum s (fun i hi => swapped_tail_integrable (F i) (hF i hi)
        (B i) (hB i hi) (hb i hi) r)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (spectralJGaussianTail_KLIntegral_eq (F i) (hF i hi) (B i) (hB i hi)
        (hb i hi) r).symm

end
end ArtinMatthews
