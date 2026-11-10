module

public import ArtinMatthews.SpectralRellichEnergy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Exact Euclidean/Cartesian coordinate and energy transfer for local Rellich. -/
namespace ArtinMatthews

open MeasureTheory Set

noncomputable def spectralPlaneEquiv : SpectralEuclidean ≃L[ℝ] (ℝ × ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

theorem spectralPlaneEquiv_apply (x : SpectralEuclidean) : spectralPlaneEquiv x = (x 0,x 1) := rfl

noncomputable def spectralPlaneMeasurableEquiv : SpectralEuclidean ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem spectralPlane_measurePreserving : MeasurePreserving spectralPlaneMeasurableEquiv volume volume :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

theorem spectralPlane_integral (F : ℝ × ℝ → ℝ) :
    (∫ x : SpectralEuclidean, F (spectralPlaneEquiv x)) = ∫ p : ℝ × ℝ, F p :=
  spectralPlane_measurePreserving.integral_comp' F

theorem spectralPlaneEquiv_single_zero : spectralPlaneEquiv (EuclideanSpace.single 0 1) = (1,0) := by
  ext <;> simp [spectralPlaneEquiv_apply]

theorem spectralPlaneEquiv_single_one : spectralPlaneEquiv (EuclideanSpace.single 1 1) = (0,1) := by
  ext <;> simp [spectralPlaneEquiv_apply]

noncomputable def spectralPlanePartialX (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  deriv (fun t : ℝ => F (t,p.2)) p.1

noncomputable def spectralPlanePartialY (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  deriv (fun t : ℝ => F (p.1,t)) p.2

theorem spectralPlanePartialX_eq_fderiv {F : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F p) : spectralPlanePartialX F p = fderiv ℝ F p (1,0) := by
  have hd : HasDerivAt (fun t : ℝ => (t,p.2)) (1,0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  exact (hF.hasFDerivAt.comp_hasDerivAt p.1 hd).deriv

theorem spectralPlanePartialY_eq_fderiv {F : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F p) : spectralPlanePartialY F p = fderiv ℝ F p (0,1) := by
  have hd : HasDerivAt (fun t : ℝ => (p.1,t)) (0,1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact (hF.hasFDerivAt.comp_hasDerivAt p.2 hd).deriv

theorem spectralPlane_coordinate_derivatives {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F)
    (x : SpectralEuclidean) :
    spectralCoordinateDerivative (F ∘ spectralPlaneEquiv) 0 x =
        spectralPlanePartialX F (spectralPlaneEquiv x) ∧
    spectralCoordinateDerivative (F ∘ spectralPlaneEquiv) 1 x =
        spectralPlanePartialY F (spectralPlaneEquiv x) := by
  have he : fderiv ℝ (F ∘ spectralPlaneEquiv) x =
      (fderiv ℝ F (spectralPlaneEquiv x)).comp spectralPlaneEquiv.toContinuousLinearMap := by
    rw [fderiv_comp x (hF.differentiable (by norm_num) _)
      spectralPlaneEquiv.differentiableAt,spectralPlaneEquiv.fderiv]
  constructor
  · rw [spectralCoordinateDerivative,he,ContinuousLinearMap.comp_apply]
    have hz : spectralPlaneEquiv.toContinuousLinearMap (EuclideanSpace.single 0 1) = (1,0) :=
      spectralPlaneEquiv_single_zero
    rw [hz,spectralPlanePartialX_eq_fderiv (hF.differentiable (by norm_num) _)]
  · rw [spectralCoordinateDerivative,he,ContinuousLinearMap.comp_apply]
    have hz : spectralPlaneEquiv.toContinuousLinearMap (EuclideanSpace.single 1 1) = (0,1) :=
      spectralPlaneEquiv_single_one
    rw [hz,spectralPlanePartialY_eq_fderiv (hF.differentiable (by norm_num) _)]

noncomputable def spectralPlaneH1Energy (F : ℝ × ℝ → ℂ) : ℝ :=
  (∫ p, ‖F p‖^2) + ∫ p, (‖spectralPlanePartialX F p‖^2+‖spectralPlanePartialY F p‖^2)

/-- The actual Cartesian H1 energy equals the Euclidean coordinate energy,
without a Jacobian or an assumed comparison constant. -/
theorem spectralPlane_energy_eq {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F) :
    spectralEuclideanH1Energy (F ∘ spectralPlaneEquiv) = spectralPlaneH1Energy F := by
  unfold spectralEuclideanH1Energy spectralPlaneH1Energy
  simp only [Function.comp_apply]
  rw [spectralPlane_integral (fun p => ‖F p‖^2)]
  congr 1
  calc
    _ = ∫ x : SpectralEuclidean, (‖spectralPlanePartialX F (spectralPlaneEquiv x)‖^2+
          ‖spectralPlanePartialY F (spectralPlaneEquiv x)‖^2) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [(spectralPlane_coordinate_derivatives hF x).1,(spectralPlane_coordinate_derivatives hF x).2]
    _ = _ := spectralPlane_integral
      (fun p => ‖spectralPlanePartialX F p‖^2+‖spectralPlanePartialY F p‖^2)

end ArtinMatthews
