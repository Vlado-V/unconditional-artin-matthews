module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import ArtinMatthews.SpectralCuspWeakRegularityLocal
public import ArtinMatthews.SpectralCuspWeakRegularityPrimitiveWeak
public import ArtinMatthews.SpectralCuspWeakRegularityWeakZero
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical positive-half-line Sobolev representatives, obtained from
actual compact-test weak identities and local integrability alone. -/
namespace ArtinMatthews.SpectralCuspWeakRegularity
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

def PositiveWeakDerivative (f g : ℝ → ℂ) : Prop :=
  ∀ (ρ : ℝ → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ → tsupport ρ ⊆ Ioi (0 : ℝ) →
    (∫ x in Ioi (0 : ℝ), deriv ρ x • f x) = -(∫ x in Ioi (0 : ℝ), ρ x • g x)

theorem positiveWeakDerivative_full {f g : ℝ → ℂ} (hw : PositiveWeakDerivative f g)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Ioi (0 : ℝ)) :
    (∫ x, deriv ρ x • f x) = -(∫ x, ρ x • g x) := by
  have H := hw ρ hρ hρc hρs
  rw [positive_test_setIntegral_eq f (tsupport_deriv_subset.trans hρs),
    positive_test_setIntegral_eq g hρs] at H
  exact H

theorem positive_weak_representation {f g : ℝ → ℂ}
    (hf : LocallyIntegrableOn f (Ioi (0 : ℝ)) volume)
    (hg : LocallyIntegrableOn g (Ioi (0 : ℝ)) volume) (hw : PositiveWeakDerivative f g) :
    ∃ z : ℂ, f =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun x => z + ∫ t in (1 : ℝ)..x, g t := by
  let F := fun x => ∫ t in (1 : ℝ)..x, g t
  have hFc : ContinuousOn F (Ioi (0 : ℝ)) := positive_primitive_continuousOn hg
  have hFl : LocallyIntegrableOn F (Ioi (0 : ℝ)) volume :=
    hFc.locallyIntegrableOn measurableSet_Ioi
  obtain ⟨z, hz⟩ := positive_weak_zero_ae_const (hf.sub hFl) (fun ρ hρ hρc hρs => by
    have hds : tsupport (deriv ρ) ⊆ Ioi (0 : ℝ) := tsupport_deriv_subset.trans hρs
    have hfi := integrable_positive_test_smul hf (hρ.continuous_deriv (by simp)) hρc.deriv hds
    have hFi := integrable_positive_test_smul hFl (hρ.continuous_deriv (by simp)) hρc.deriv hds
    simp_rw [Pi.sub_apply, smul_sub]
    rw [integral_sub hfi hFi, positiveWeakDerivative_full hw ρ hρ hρc hρs]
    change -(∫ x, ρ x • g x) - (∫ x, deriv ρ x • (∫ t in (1 : ℝ)..x, g t)) = 0
    rw [positive_primitive_weak_derivative_complex hg ρ hρ hρc hρs, sub_self])
  refine ⟨z, ?_⟩
  filter_upwards [hz] with x hx
  exact sub_eq_iff_eq_add.mp hx

theorem positive_weak_continuous_representative {f g : ℝ → ℂ}
    (hf : LocallyIntegrableOn f (Ioi (0 : ℝ)) volume)
    (hg : LocallyIntegrableOn g (Ioi (0 : ℝ)) volume) (hw : PositiveWeakDerivative f g) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Ioi (0 : ℝ)) ∧
      f =ᵐ[volume.restrict (Ioi (0 : ℝ))] F := by
  obtain ⟨z, hz⟩ := positive_weak_representation hf hg hw
  exact ⟨fun x => z + ∫ t in (1 : ℝ)..x, g t,
    continuousOn_const.add (positive_primitive_continuousOn hg), hz⟩

theorem positive_interval_integral_congr {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in a..b, f t) = ∫ t in a..b, g t := by
  apply intervalIntegral.integral_congr_ae
  have H := (ae_restrict_iff' measurableSet_Ioi).mp hfg
  filter_upwards [H] with x hx hmem
  exact hx (lt_of_lt_of_le (lt_min ha hb) (uIoc_subset_uIcc hmem).1)

theorem positive_primitive_hasDerivAt {G : ℝ → ℂ}
    (hG : ContinuousOn G (Ioi (0 : ℝ))) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x => ∫ t in (1 : ℝ)..x, G t) (G y) y :=
  intervalIntegral.integral_hasDerivAt_right
    (positive_interval_integrable (hG.locallyIntegrableOn measurableSet_Ioi) zero_lt_one hy)
    (hG.stronglyMeasurableAtFilter isOpen_Ioi y hy)
    (hG.continuousAt (Ioi_mem_nhds hy))

/-- Any continuous representatives of a true weak derivative pair have the
claimed classical derivative; no representative regularity is postulated. -/
theorem positiveWeakDerivative_hasDerivAt {f g F G : ℝ → ℂ}
    (hf : LocallyIntegrableOn f (Ioi (0 : ℝ)) volume)
    (hg : LocallyIntegrableOn g (Ioi (0 : ℝ)) volume) (hw : PositiveWeakDerivative f g)
    (hF : ContinuousOn F (Ioi (0 : ℝ))) (hG : ContinuousOn G (Ioi (0 : ℝ)))
    (hfF : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] F)
    (hgG : g =ᵐ[volume.restrict (Ioi (0 : ℝ))] G) :
    ∀ y > 0, HasDerivAt F (G y) y := by
  obtain ⟨z, hz⟩ := positive_weak_representation hf hg hw
  let H := fun x => z + ∫ t in (1 : ℝ)..x, G t
  have hH : ContinuousOn H (Ioi (0 : ℝ)) :=
    continuousOn_const.add (positive_primitive_continuousOn (hG.locallyIntegrableOn measurableSet_Ioi))
  have hfH : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] H := by
    filter_upwards [hz, ae_restrict_mem measurableSet_Ioi] with x hx hxS
    rw [hx]
    exact congrArg (fun v : ℂ => z + v) (positive_interval_integral_congr hgG zero_lt_one hxS)
  have hFH := Measure.eqOn_open_of_ae_eq (hfF.symm.trans hfH) isOpen_Ioi hF hH
  intro y hy
  have hd : HasDerivAt H (G y) y := (positive_primitive_hasDerivAt hG hy).const_add z
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with x hx
  exact hFH hx

end
end ArtinMatthews.SpectralCuspWeakRegularity
