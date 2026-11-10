module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The real Poisson peak, including its normalization and a dominated
approximation theorem for a varying, uniformly bounded amplitude. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralPoissonPeak (ε x : ℝ) : ℝ := ε / (ε^2+x^2)

theorem spectralPoissonPeak_rescale (ε u : ℝ) (hε : ε ≠ 0) :
    ε * spectralPoissonPeak ε (ε*u) = (1+u^2)⁻¹ := by
  unfold spectralPoissonPeak
  have h : 1+u^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp

theorem spectralPoissonPeak_integral_rescale (ε t : ℝ) (hε : 0 < ε)
    (G : ℝ → ℂ) :
    (∫ v : ℝ, spectralPoissonPeak ε (v-t) • G v) =
      ∫ u : ℝ, (1+u^2)⁻¹ • G (t+ε*u) := by
  let F : ℝ → ℂ := fun v => spectralPoissonPeak ε (v-t) • G v
  have hscale := Measure.integral_comp_mul_left (fun v : ℝ => F (t+v)) ε
  rw [integral_add_left_eq_self] at hscale
  have habs : |ε⁻¹| = ε⁻¹ := abs_of_pos (inv_pos.mpr hε)
  rw [habs] at hscale
  calc
    (∫ v : ℝ, spectralPoissonPeak ε (v-t) • G v) =
        ε • (∫ u : ℝ, F (t+ε*u)) := by
          rw [hscale, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
    _ = ∫ u : ℝ, (1+u^2)⁻¹ • G (t+ε*u) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with u
      dsimp [F]
      rw [add_sub_cancel_left, ← mul_assoc, ← Complex.ofReal_mul,
        spectralPoissonPeak_rescale ε u hε.ne']

theorem spectralPoissonPeak_integral (ε t : ℝ) (hε : 0 < ε) :
    (∫ v : ℝ, (spectralPoissonPeak ε (v-t) : ℂ)) = (Real.pi : ℂ) := by
  have h := spectralPoissonPeak_integral_rescale ε t hε (fun _ => (1 : ℂ))
  simpa only [Complex.real_smul, mul_one, integral_complex_ofReal,
    integral_univ_inv_one_add_sq] using h

theorem spectralPoissonPeak_approximation (t : ℝ) (G : ℝ × ℝ → ℂ)
    (hcont : ContinuousAt G (0,t))
    (hmeas : ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun u : ℝ => G (ε,t+ε*u)))
    (C : ℝ)
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ v : ℝ, ‖G (ε,v)‖ ≤ C) :
    Tendsto (fun ε : ℝ => ∫ v : ℝ, spectralPoissonPeak ε (v-t) • G (ε,v))
      (𝓝[>] (0 : ℝ)) (𝓝 ((Real.pi : ℂ)*G (0,t))) := by
  have hlim : Tendsto (fun ε : ℝ =>
      ∫ u : ℝ, (1+u^2)⁻¹ • G (ε,t+ε*u))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ u : ℝ, (1+u^2)⁻¹ • G (0,t))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun u : ℝ => (1+u^2)⁻¹*C)
    · filter_upwards [hmeas] with ε hε
      have hc : Continuous (fun u : ℝ => (1+u^2)⁻¹) :=
        (show Continuous (fun u : ℝ => 1+u^2) by fun_prop).inv₀
          (fun u => ne_of_gt (show 0 < 1+u^2 by positivity))
      exact hc.aestronglyMeasurable.smul hε
    · filter_upwards [hbound] with ε hε
      filter_upwards with u
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hε _) (by positivity)
    · exact integrable_inv_one_add_sq.mul_const C
    · filter_upwards with u
      have ht : Tendsto (fun ε : ℝ => (ε,t+ε*u)) (𝓝[>] (0 : ℝ)) (𝓝 (0,t)) := by
        have hc : ContinuousAt (fun ε : ℝ => (ε,t+ε*u)) 0 := by fun_prop
        simpa only [zero_mul,add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_const_nhds.smul (hcont.tendsto.comp ht)
  have heq : (∫ u : ℝ, (1+u^2)⁻¹ • G (0,t)) = (Real.pi : ℂ)*G (0,t) := by
    rw [integral_smul_const, integral_univ_inv_one_add_sq, Complex.real_smul]
  rw [heq] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (spectralPoissonPeak_integral_rescale ε t hε (fun v => G (ε,v))).symm

end ArtinMatthews
