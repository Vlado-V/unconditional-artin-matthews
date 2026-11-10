module

public import ArtinMatthews.SpectralCuspTail
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import ArtinMatthews.SpectralHyperbolicCoordinates
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Cusp escape-of-mass control for Mathlib's actual hyperbolic measure. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff

namespace ArtinMatthews

def hyperbolicCuspStrip (w Y : ℝ) : Set UpperHalfPlane :=
  {z | z.re ∈ Ioc 0 w ∧ Y < z.im}

private theorem cusp_coordinate_mass_integrable {F : ℝ × ℝ → ℂ}
    (hF : Continuous F) {w Y : ℝ} (hw : 0 < w)
    (hfinite : IntegrableOn (fun y => cuspHorizontalMass F w y / y ^ 2) (Ioi Y)) :
    Integrable (fun p : ℝ × ℝ => ‖F p‖ ^ 2 / p.2 ^ 2)
      ((volume.restrict (Ioc 0 w)).prod (volume.restrict (Ioi Y))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖F p‖ ^ 2 / p.2 ^ 2)
      ((volume.restrict (Ioc 0 w)).prod (volume.restrict (Ioi Y))) :=
    ((hF.norm.pow 2).measurable.div (measurable_snd.pow_const 2)).aestronglyMeasurable
  apply (integrable_prod_iff' hm).mpr
  constructor
  · apply Eventually.of_forall
    intro y
    have hc : Continuous (fun x : ℝ => ‖F (x, y)‖ ^ 2) :=
      (hF.comp (continuous_id.prodMk continuous_const)).norm.pow 2
    change Integrable (fun x => ‖F (x, y)‖ ^ 2 / y ^ 2) (volume.restrict (Ioc 0 w))
    exact ((hc.integrableOn_Icc (μ := volume) (a := 0) (b := w)).mono_set
      Ioc_subset_Icc_self).div_const (y ^ 2)
  · have he : (fun y => ∫ x in Ioc 0 w, ‖‖F (x, y)‖ ^ 2 / y ^ 2‖) =
        (fun y => cuspHorizontalMass F w y / y ^ 2) := by
      funext y
      simp only [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)),
        integral_div, cuspHorizontalMass, intervalIntegral.integral_of_le hw.le]
    rw [he]
    exact hfinite

/-- The coordinate tail mass is the integral against the invariant measure,
with all Fubini integrability premises discharged by the finite-energy bound. -/
theorem hyperbolic_cusp_mass_eq {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (hfinite : IntegrableOn (fun y => cuspHorizontalMass F w y / y ^ 2) (Ioi Y)) :
    (∫ z : UpperHalfPlane in hyperbolicCuspStrip w Y, ‖F (z.re, z.im)‖ ^ 2) =
      ∫ y in Ioi Y, cuspHorizontalMass F w y / y ^ 2 := by
  have he := upperHalfPlane_setIntegral_coordinates (fun p => ‖F p‖ ^ 2)
    (S := (Ioc 0 w) ×ˢ (Ioi Y))
    (measurableSet_Ioc.prod measurableSet_Ioi)
    (fun p hp => hY.trans hp.2)
  change (∫ z : UpperHalfPlane in hyperbolicCuspStrip w Y, ‖F (z.re, z.im)‖ ^ 2) =
    ∫ p in (Ioc 0 w) ×ˢ (Ioi Y), ‖F p‖ ^ 2 / p.2 ^ 2 at he
  rw [he]
  change (∫ p, ‖F p‖ ^ 2 / p.2 ^ 2
    ∂(volume.prod volume).restrict ((Ioc 0 w) ×ˢ (Ioi Y))) = _
  rw [← Measure.prod_restrict]
  rw [integral_prod_symm _ (cusp_coordinate_mass_integrable hF hw hfinite)]
  apply integral_congr_ae
  filter_upwards with y
  rw [integral_div, cuspHorizontalMass, intervalIntegral.integral_of_le hw.le]

/-- Actual H² cusp-tail mass decays quadratically in height for zero-mean
sections with finite horizontal Dirichlet energy. -/
theorem hyperbolic_cusp_tail_bound {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (hsmooth : ∀ y ∈ Ioi Y, ContDiff ℝ ∞ (fun x => F (x, y)))
    (hmean : ∀ y ∈ Ioi Y, (∫ x in (0 : ℝ)..w, F (x, y)) = 0)
    (henergy : IntegrableOn (cuspHorizontalEnergy F w) (Ioi Y)) :
    (∫ z : UpperHalfPlane in hyperbolicCuspStrip w Y, ‖F (z.re, z.im)‖ ^ 2) ≤
      (w ^ 2 / Y ^ 2) * ∫ y in Ioi Y, cuspHorizontalEnergy F w y := by
  obtain ⟨hfinite, hbound⟩ := cusp_horizontal_tail_bound hF hw hY hsmooth hmean henergy
  rw [hyperbolic_cusp_mass_eq hF hw hY hfinite]
  exact hbound

end ArtinMatthews
