module

public import ArtinMatthews.SpectralGamma0AmbientResolvent
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap


set_option backward.privateInPublic true
@[expose] public section

/-! Holomorphic dependence of the true full ambient resolvent off the
nonnegative real ray. This concerns the ambient operator, not yet agreement
with a continued Eisenstein section. -/
noncomputable section
open Set Filter Topology
namespace ArtinMatthews

theorem gamma0EnergyResolventPencil_isUnit (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re < ‖z‖) : IsUnit (gamma0EnergyResolventPencil N z) := by
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  constructor
  · intro u v huv
    apply (gamma0EnergyRotatedEquiv N z hz).injective
    change spectralResolventRotation z • gamma0EnergyResolventPencil N z u=
      spectralResolventRotation z • gamma0EnergyResolventPencil N z v
    rw [huv]
  · intro v
    let u := (gamma0EnergyRotatedEquiv N z hz).symm (spectralResolventRotation z • v)
    refine ⟨u,?_⟩
    have he := (gamma0EnergyRotatedEquiv N z hz).apply_symm_apply (spectralResolventRotation z • v)
    change spectralResolventRotation z • gamma0EnergyResolventPencil N z u=
      spectralResolventRotation z • v at he
    have h := congrArg (fun w : gamma0EnergySpace N => (spectralResolventRotation z)⁻¹ • w) he
    simpa only [smul_smul,inv_mul_cancel₀ (spectralResolventRotation_ne_zero z hz),one_smul] using h

def gamma0AmbientResolventFamily (N : ℕ) [NeZero N] (z : ℂ) :
    Gamma0RegionL2 N →L[ℂ] Gamma0RegionL2 N :=
  (gamma0EnergyInclusion N).comp
    ((Ring.inverse (gamma0EnergyResolventPencil N z)).comp (gamma0EnergyMassAdjoint N))

theorem gamma0AmbientResolventFamily_eq (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re < ‖z‖) :
    gamma0AmbientResolventFamily N z=gamma0AmbientResolvent N z hz := by
  apply ContinuousLinearMap.ext
  intro F
  have hp := gamma0AmbientWeakResolvent_pencil N z hz F
  have hi := congrArg (fun A : gamma0EnergySpace N →L[ℂ] gamma0EnergySpace N =>
      A (gamma0AmbientWeakResolvent N z hz F))
    (Ring.inverse_mul_cancel (gamma0EnergyResolventPencil N z)
      (gamma0EnergyResolventPencil_isUnit N z hz))
  change (Ring.inverse (gamma0EnergyResolventPencil N z))
      (gamma0EnergyResolventPencil N z (gamma0AmbientWeakResolvent N z hz F))=
        gamma0AmbientWeakResolvent N z hz F at hi
  rw [hp] at hi
  exact congrArg (gamma0EnergyInclusion N) hi

section GeneralAnalytic
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

omit [CompleteSpace E] in
theorem spectralOperatorPencil_analyticAt (T : E →L[ℂ] E) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => ContinuousLinearMap.id ℂ E-(w+1) • T) z := by
  have h0 : AnalyticAt ℂ (fun _ : ℂ => ContinuousLinearMap.id ℂ E) z := analyticAt_const
  have h1 : AnalyticAt ℂ (fun w : ℂ => w+1) z := analyticAt_id.add analyticAt_const
  have h2 : AnalyticAt ℂ (fun _ : ℂ => T) z := analyticAt_const
  exact h0.sub (h1.smul h2)

theorem spectralOperatorPencilInverse_analyticAt (T : E →L[ℂ] E) (z : ℂ)
    (hz : IsUnit (ContinuousLinearMap.id ℂ E-(z+1) • T)) :
    AnalyticAt ℂ (fun w : ℂ => Ring.inverse (ContinuousLinearMap.id ℂ E-(w+1) • T)) z := by
  exact (analyticOnNhd_inverse (𝕜 := ℂ) (A := E →L[ℂ] E) _ hz).comp
    (f := fun w : ℂ => ContinuousLinearMap.id ℂ E-(w+1) • T)
    (spectralOperatorPencil_analyticAt T z)

omit [CompleteSpace E] in
theorem spectralOperatorSandwich_analyticAt (T : ℂ → E →L[ℂ] E)
    (hT : AnalyticAt ℂ T z) (J : E →L[ℂ] H) (K : H →L[ℂ] E) :
    AnalyticAt ℂ (fun w => J.comp ((T w).comp K)) z := by
  let B : (E →L[ℂ] E) →L[ℂ] (H →L[ℂ] E) :=
    ContinuousLinearMap.flip (E := E →L[ℂ] E) (F := H →L[ℂ] E) (G := H →L[ℂ] E)
      (σ₁₃ := RingHom.id ℂ) (σ₂₃ := RingHom.id ℂ) (ContinuousLinearMap.compL ℂ H E E) K
  let A : (E →L[ℂ] E) →L[ℂ] (H →L[ℂ] H) :=
    (ContinuousLinearMap.compL ℂ H E H J).comp B
  exact (A.analyticAt (T z)).comp hT

end GeneralAnalytic

theorem gamma0EnergyResolventPencil_analyticAt (N : ℕ) [NeZero N] (z : ℂ) :
    AnalyticAt ℂ (gamma0EnergyResolventPencil N) z :=
  spectralOperatorPencil_analyticAt ((gamma0EnergyMassAdjoint N).comp (gamma0EnergyInclusion N)) z

theorem gamma0AmbientResolventFamily_analyticAt (N : ℕ) [NeZero N]
    (z : ℂ) (hz : z.re < ‖z‖) : AnalyticAt ℂ (gamma0AmbientResolventFamily N) z := by
  have hi := spectralOperatorPencilInverse_analyticAt
    ((gamma0EnergyMassAdjoint N).comp (gamma0EnergyInclusion N)) z
    (gamma0EnergyResolventPencil_isUnit N z hz)
  exact spectralOperatorSandwich_analyticAt _ hi (gamma0EnergyInclusion N) (gamma0EnergyMassAdjoint N)

end ArtinMatthews
