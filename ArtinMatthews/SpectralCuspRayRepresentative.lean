module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import ArtinMatthews.SpectralCuspRayLocal
public import ArtinMatthews.SpectralCuspRayPrimitiveWeak
public import ArtinMatthews.SpectralCuspRayWeakZero
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

/-! Canonical positive cusp-ray Sobolev representatives, obtained from
actual compact-test weak identities and local integrability alone. -/
namespace ArtinMatthews.SpectralCuspRayRegularity
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
variable {Y : ℝ}

def RayWeakDerivative (f g : ℝ → ℂ) : Prop :=
  ∀ (ρ : ℝ → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ → tsupport ρ ⊆ Ioi Y →
    (∫ x in Ioi Y, deriv ρ x • f x) = -(∫ x in Ioi Y, ρ x • g x)

theorem rayWeakDerivative_full {f g : ℝ → ℂ} (hw : RayWeakDerivative (Y:=Y) f g)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Ioi Y) :
    (∫ x, deriv ρ x • f x) = -(∫ x, ρ x • g x) := by
  have H := hw ρ hρ hρc hρs
  rw [ray_test_setIntegral_eq f (tsupport_deriv_subset.trans hρs),
    ray_test_setIntegral_eq g hρs] at H
  exact H

theorem ray_weak_representation (hY : 0≤Y) {f g : ℝ → ℂ}
    (hf : LocallyIntegrableOn f (Ioi Y) volume)
    (hg : LocallyIntegrableOn g (Ioi Y) volume) (hw : RayWeakDerivative (Y:=Y) f g) :
    ∃ z : ℂ, f =ᵐ[volume.restrict (Ioi Y)]
      fun x => z + ∫ t in (Y+1)..x, g t := by
  let F := fun x => ∫ t in (Y+1)..x, g t
  have hFc : ContinuousOn F (Ioi Y) := ray_primitive_continuousOn hg
  have hFl : LocallyIntegrableOn F (Ioi Y) volume :=
    hFc.locallyIntegrableOn measurableSet_Ioi
  obtain ⟨z, hz⟩ := ray_weak_zero_ae_const hY (hf.sub hFl) (fun ρ hρ hρc hρs => by
    have hds : tsupport (deriv ρ) ⊆ Ioi Y := tsupport_deriv_subset.trans hρs
    have hfi := integrable_ray_test_smul hf (hρ.continuous_deriv (by simp)) hρc.deriv hds
    have hFi := integrable_ray_test_smul hFl (hρ.continuous_deriv (by simp)) hρc.deriv hds
    simp_rw [Pi.sub_apply, smul_sub]
    rw [integral_sub hfi hFi, rayWeakDerivative_full hw ρ hρ hρc hρs]
    change -(∫ x, ρ x • g x) - (∫ x, deriv ρ x • (∫ t in (Y+1)..x, g t)) = 0
    rw [ray_primitive_weak_derivative_complex hg ρ hρ hρc hρs, sub_self])
  refine ⟨z, ?_⟩
  filter_upwards [hz] with x hx
  exact sub_eq_iff_eq_add.mp hx

theorem ray_weak_continuous_representative (hY : 0≤Y) {f g : ℝ → ℂ}
    (hf : LocallyIntegrableOn f (Ioi Y) volume)
    (hg : LocallyIntegrableOn g (Ioi Y) volume) (hw : RayWeakDerivative (Y:=Y) f g) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Ioi Y) ∧
      f =ᵐ[volume.restrict (Ioi Y)] F := by
  obtain ⟨z, hz⟩ := ray_weak_representation hY hf hg hw
  exact ⟨fun x => z + ∫ t in (Y+1)..x, g t,
    continuousOn_const.add (ray_primitive_continuousOn hg), hz⟩

theorem ray_interval_integral_congr {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume.restrict (Ioi Y)] g) {a b : ℝ} (ha : Y < a) (hb : Y < b) :
    (∫ t in a..b, f t) = ∫ t in a..b, g t := by
  apply intervalIntegral.integral_congr_ae
  have H := (ae_restrict_iff' measurableSet_Ioi).mp hfg
  filter_upwards [H] with x hx hmem
  exact hx (lt_of_lt_of_le (lt_min ha hb) (uIoc_subset_uIcc hmem).1)

theorem ray_primitive_hasDerivAt {G : ℝ → ℂ}
    (hG : ContinuousOn G (Ioi Y)) {y : ℝ} (hy : Y < y) :
    HasDerivAt (fun x => ∫ t in (Y+1)..x, G t) (G y) y :=
  intervalIntegral.integral_hasDerivAt_right
    (ray_interval_integrable (hG.locallyIntegrableOn measurableSet_Ioi) (by linarith : Y<Y+1) hy)
    (hG.stronglyMeasurableAtFilter isOpen_Ioi y hy)
    (hG.continuousAt (Ioi_mem_nhds hy))

/-- Any continuous representatives of a true weak derivative pair have the
claimed classical derivative; no representative regularity is postulated. -/
theorem rayWeakDerivative_hasDerivAt (hY : 0≤Y) {f g F G : ℝ → ℂ}
    (hf : LocallyIntegrableOn f (Ioi Y) volume)
    (hg : LocallyIntegrableOn g (Ioi Y) volume) (hw : RayWeakDerivative (Y:=Y) f g)
    (hF : ContinuousOn F (Ioi Y)) (hG : ContinuousOn G (Ioi Y))
    (hfF : f =ᵐ[volume.restrict (Ioi Y)] F)
    (hgG : g =ᵐ[volume.restrict (Ioi Y)] G) :
    ∀ y > Y, HasDerivAt F (G y) y := by
  obtain ⟨z, hz⟩ := ray_weak_representation hY hf hg hw
  let H := fun x => z + ∫ t in (Y+1)..x, G t
  have hH : ContinuousOn H (Ioi Y) :=
    continuousOn_const.add (ray_primitive_continuousOn (hG.locallyIntegrableOn measurableSet_Ioi))
  have hfH : f =ᵐ[volume.restrict (Ioi Y)] H := by
    filter_upwards [hz, ae_restrict_mem measurableSet_Ioi] with x hx hxS
    rw [hx]
    exact congrArg (fun v : ℂ => z + v) (ray_interval_integral_congr hgG (by linarith : Y<Y+1) hxS)
  have hFH := Measure.eqOn_open_of_ae_eq (hfF.symm.trans hfH) isOpen_Ioi hF hH
  intro y hy
  have hd : HasDerivAt H (G y) y := (ray_primitive_hasDerivAt hG hy).const_add z
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with x hx
  exact hFH hx

end
end ArtinMatthews.SpectralCuspRayRegularity
