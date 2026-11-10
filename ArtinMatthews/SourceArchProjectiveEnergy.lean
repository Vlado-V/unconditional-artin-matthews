module

public import ArtinMatthews.SourceArchProjectiveActionSmooth
public import ArtinMatthews.SourceHyperbolicEnergy
public import ArtinMatthews.SourceArchMobiusDifferential
public import ArtinMatthews.SourceArchMobiusEnergy
public import ArtinMatthews.SourceArchPGLSurjectivity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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

/-! The actual full projective action preserves hyperbolic Dirichlet energy. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix OAI.CubicEisenstein SourceHyperbolicGreen MeasureTheory Filter
open scoped MatrixGroups Topology ContDiff
noncomputable section

theorem sourceArchEuclideanProjectiveAction_isometric_differential (a : PGL(2, ℂ))
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    ∃ (r : ℝ) (e : EuclideanSpatial ≃ₗᵢ[ℝ] EuclideanSpatial), 0 < r ∧
      HasFDerivAt (sourceArchEuclideanProjectiveAction a)
        (r • e.toContinuousLinearEquiv.toContinuousLinearMap) p ∧
      sourceArchEuclideanProjectiveAction a p 2 = r * p 2 := by
  obtain ⟨s, rfl⟩ := sourceArchSpecialLinear_toPGL_surjective a
  obtain ⟨r, e, hr, hD, hY⟩ := sourceArchMobiusEuclidean_isometric_differential s p hp
  have he : sourceArchEuclideanProjectiveAction (SpecialLinearGroup.toPGL s) =ᶠ[𝓝 p]
      sourceArchMobiusEuclidean s := by
    filter_upwards [sourceArch_positive_eventually p hp] with q hq
    exact sourceArchEuclideanProjectiveAction_specialLinear s q hq
  refine ⟨r, e, hr, hD.congr_of_eventuallyEq he, ?_⟩
  rw [he.self_of_nhds]
  exact hY

theorem sourceArchEuclideanProjectiveAction_fderiv_norm (a : PGL(2, ℂ))
    (p v : EuclideanSpatial) (hp : 0 < p 2) :
    ‖fderiv ℝ (sourceArchEuclideanProjectiveAction a) p v‖ =
      (sourceArchEuclideanProjectiveAction a p 2 / p 2) * ‖v‖ := by
  obtain ⟨r, e, hr, hD, hY⟩ := sourceArchEuclideanProjectiveAction_isometric_differential a p hp
  rw [hD.fderiv]
  change ‖r • e v‖ = (sourceArchEuclideanProjectiveAction a p 2 / p 2) * ‖v‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, e.norm_map, hY,
    mul_div_cancel_right₀ r hp.ne']

theorem sourceArchEuclideanProjectiveAction_metric (a : PGL(2, ℂ))
    (p v : EuclideanSpatial) (hp : 0 < p 2) :
    (p 2) ^ 2 * ‖fderiv ℝ (sourceArchEuclideanProjectiveAction a) p v‖ ^ 2 =
      (sourceArchEuclideanProjectiveAction a p 2) ^ 2 * ‖v‖ ^ 2 := by
  rw [sourceArchEuclideanProjectiveAction_fderiv_norm a p v hp]
  field_simp [hp.ne']

theorem sourceArchEuclideanProjectiveAction_gradientEnergy (a : PGL(2, ℂ))
    (f : EuclideanSpatial → ℂ) (p : EuclideanSpatial) (hp : 0 < p 2)
    (hf : DifferentiableAt ℝ f (sourceArchEuclideanProjectiveAction a p)) :
    gradientEnergy (f ∘ sourceArchEuclideanProjectiveAction a) p =
      gradientEnergy f (sourceArchEuclideanProjectiveAction a p) := by
  obtain ⟨r, e, _hr, hD, hY⟩ := sourceArchEuclideanProjectiveAction_isometric_differential a p hp
  exact sourceArch_similarity_gradientEnergy _ p r e hD hY f hf

theorem sourceArchEuclideanProjectiveAction_gradientEnergy_ae (a : PGL(2, ℂ))
    (f : EuclideanSpatial → ℂ) (hf : ∀ p, 0 < p 2 → DifferentiableAt ℝ f p) :
    gradientEnergy (f ∘ sourceArchEuclideanProjectiveAction a) =ᵐ[hyperbolicEuclideanVolume]
      (gradientEnergy f) ∘ sourceArchEuclideanProjectiveAction a := by
  filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
  exact sourceArchEuclideanProjectiveAction_gradientEnergy a f p hp
    (hf _ (sourceArchUpperEuclideanMap_positive _))

theorem sourceArchEuclideanProjectiveAction_gradientEnergy_integrable (a : PGL(2, ℂ))
    (f : EuclideanSpatial → ℂ) (hf : ∀ p, 0 < p 2 → DifferentiableAt ℝ f p)
    (hE : Integrable (gradientEnergy f) hyperbolicEuclideanVolume) :
    Integrable (gradientEnergy (f ∘ sourceArchEuclideanProjectiveAction a))
      hyperbolicEuclideanVolume :=
  ((sourceArchEuclideanProjectiveAction_preserving a).integrable_comp_of_integrable hE).congr
    (sourceArchEuclideanProjectiveAction_gradientEnergy_ae a f hf).symm

theorem sourceArchEuclideanProjectiveAction_dirichlet (a : PGL(2, ℂ))
    (f : EuclideanSpatial → ℂ)
    (hf : ∀ p, 0 < p 2 → DifferentiableAt ℝ f p)
    (hE : Integrable (gradientEnergy f) hyperbolicEuclideanVolume) :
    (∫ p, gradientEnergy (f ∘ sourceArchEuclideanProjectiveAction a) p
      ∂hyperbolicEuclideanVolume) = ∫ p, gradientEnergy f p ∂hyperbolicEuclideanVolume := by
  have he := sourceArchEuclideanProjectiveAction_gradientEnergy_ae a f hf
  rw [integral_congr_ae he]
  have hm := sourceArchEuclideanProjectiveAction_preserving a
  have hmeas : AEStronglyMeasurable (gradientEnergy f)
      (Measure.map (sourceArchEuclideanProjectiveAction a) hyperbolicEuclideanVolume) := by
    rw [hm.map_eq]
    exact hE.aestronglyMeasurable
  simpa only [hm.map_eq, Function.comp_apply] using (integral_map hm.aemeasurable hmeas).symm

theorem sourceArchEuclideanProjectiveAction_dirichlet_core (a : PGL(2, ℂ))
    (f : EuclideanSpatial → ℂ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ euclideanUpperHalf) :
    (∫ p, gradientEnergy (f ∘ sourceArchEuclideanProjectiveAction a) p
      ∂hyperbolicEuclideanVolume) = ∫ p, gradientEnergy f p ∂hyperbolicEuclideanVolume :=
  sourceArchEuclideanProjectiveAction_dirichlet a f
    (fun _ _ => hf.contDiffAt.differentiableAt (by norm_num)) (gradientEnergy_integrable hf hc hs)

end
end ArtinMatthews.SourceArchJacquet
