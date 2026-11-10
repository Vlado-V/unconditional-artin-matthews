module

public import ArtinMatthews.SpectralCompactLaplace
public import ArtinMatthews.SpectralKLCompactOrder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex OAI.CubicEisenstein
noncomputable section

/-- The compact K transform with the x integration done first.
The logarithmic Schläfli kernel supplies the absolute Fubini bound. -/
theorem spectralKLCompactOrderTransform_laplace (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (ν : ℂ) :
    let g := spectralKLPhysicalCompactDiv f
    Integrable (fun u : ℝ => Complex.exp (ν*(u : ℂ))*
      spectralCompactLaplace g (Real.cosh u : ℂ)) ∧
    spectralKLCompactOrderTransform f ν =
      (1/2 : ℂ)*(∫ u : ℝ, Complex.exp (ν*(u : ℂ))*
        spectralCompactLaplace g (Real.cosh u : ℂ)) := by
  let g := spectralKLPhysicalCompactDiv f
  let F (u x : ℝ) := spectralKLogKernel ν x u*g x
  have hg := spectralKLPhysicalCompactDiv_continuous f hf hp
  have hgc := spectralKLPhysicalCompactDiv_hasCompactSupport f hc
  have hgI := spectralKLPhysicalCompactDiv_integrable f hf hc hp
  obtain ⟨a,ha,hasupp⟩ := spectral_compact_positive_lower_bound f hc hp
  have hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2) := by
    dsimp only [F,spectralKLogKernel]
    exact (by fun_prop : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((-(p.2*Real.cosh p.1) : ℝ) + ν*(p.1 : ℂ)))).mul (hg.comp continuous_snd)
  have he (u x : ℝ) : F u x = Complex.exp (ν*(u : ℂ))*
      (Complex.exp (-(x : ℂ)*(Real.cosh u : ℂ))*g x) := by
    dsimp only [F,spectralKLogKernel]
    rw [Complex.exp_add,Complex.ofReal_neg,Complex.ofReal_mul]
    ring
  have hi (u : ℝ) : Integrable (F u) := by
    refine ((spectralCompactLaplace_integrable g hg hgc (Real.cosh u : ℂ)).const_mul
      (Complex.exp (ν*(u : ℂ)))).congr ?_
    exact ae_of_all _ fun x => (he u x).symm
  have hnorm (u x : ℝ) : ‖F u x‖ ≤ ‖spectralKLogKernel ν a u‖*‖g x‖ := by
    by_cases hx : f x = 0
    · simp [F,g,spectralKLPhysicalCompactDiv,hx]
    · have hax := hasupp x (subset_tsupport f hx)
      dsimp only [F]
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      unfold spectralKLogKernel
      simp only [Complex.norm_exp,Complex.add_re,Complex.ofReal_re]
      apply Real.exp_le_exp.mpr
      linarith [mul_le_mul_of_nonneg_right hax (Real.cosh_pos u).le]
  let M := ∫ x : ℝ, ‖g x‖
  have hnormI (u : ℝ) : (∫ x : ℝ, ‖F u x‖) ≤ M*‖spectralKLogKernel ν a u‖ := by
    calc
      _ ≤ ∫ x : ℝ, ‖spectralKLogKernel ν a u‖*‖g x‖ :=
        integral_mono_ae (hi u).norm (hgI.norm.const_mul _) (ae_of_all _ (hnorm u))
      _ = _ := by rw [integral_const_mul]; exact mul_comm _ _
  have hProd : Integrable (fun p : ℝ × ℝ => F p.1 p.2) ((volume : Measure ℝ).prod volume) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hi,?_⟩
    apply ((spectralKLogKernel_integrable ν ha).norm.const_mul M).mono'
      hF.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards with u
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hnormI u
  have hinner (u : ℝ) : (∫ x : ℝ, F u x) =
      Complex.exp (ν*(u : ℂ))*spectralCompactLaplace g (Real.cosh u : ℂ) := by
    rw [spectralCompactLaplace,← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ (he u))
  refine ⟨hProd.integral_prod_left.congr (ae_of_all _ hinner),?_⟩
  unfold spectralKLCompactOrderTransform
  calc
    _ = (1/2 : ℂ)*(∫ x : ℝ, ∫ u : ℝ, F u x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : 0 < x
      · change schlafliBesselK ν x*g x = _
        rw [schlafliBesselK_hyperbolic_integral ν hx]
        have hi' : (∫ u : ℝ, F u x) = (∫ u : ℝ, spectralKLogKernel ν x u)*g x := by
          simp only [F,integral_mul_const]
        rw [hi',mul_assoc]
      · have hzero : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hp hs))
        simp [F,g,spectralKLCompactOrderIntegrand,spectralKLPhysicalCompactDiv,hzero]
    _ = (1/2 : ℂ)*(∫ u : ℝ, ∫ x : ℝ, F u x) := by
      rw [integral_integral_swap (f := F) hProd]
    _ = _ := by simp_rw [hinner]; rfl

end
end ArtinMatthews
