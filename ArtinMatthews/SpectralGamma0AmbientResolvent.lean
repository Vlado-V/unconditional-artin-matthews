module

public import ArtinMatthews.SpectralResolventRotation


set_option backward.privateInPublic true
@[expose] public section

/-! The full ambient Γ₀(N) resolvent from its actual completed energy form.
The coercive rotation is proved; no cuspidal restriction or spectral premise. -/
noncomputable section
open scoped InnerProductSpace
namespace ArtinMatthews

def gamma0EnergyMassAdjoint (N : ℕ) [NeZero N] : Gamma0RegionL2 N →L[ℂ] gamma0EnergySpace N :=
  ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := gamma0EnergySpace N)
    (F := Gamma0RegionL2 N) (gamma0EnergyInclusion N)

theorem gamma0EnergyMassAdjoint_inner (N : ℕ) [NeZero N]
    (v : gamma0EnergySpace N) (F : Gamma0RegionL2 N) :
    inner ℂ v (gamma0EnergyMassAdjoint N F)=inner ℂ (gamma0EnergyInclusion N v) F := by
  have h := gamma0WeakSolution_equation N F v
  rw [gamma0WeakSolution_eq_adjoint] at h
  calc
    inner ℂ v (gamma0EnergyMassAdjoint N F)=
        (starRingEnd ℂ) (inner ℂ (gamma0EnergyMassAdjoint N F) v) :=
      (inner_conj_symm (𝕜 := ℂ) v (gamma0EnergyMassAdjoint N F)).symm
    _=(starRingEnd ℂ) (inner ℂ F (gamma0EnergyInclusion N v)) := congrArg (starRingEnd ℂ) h
    _=inner ℂ (gamma0EnergyInclusion N v) F :=
      inner_conj_symm (𝕜 := ℂ) (gamma0EnergyInclusion N v) F

def gamma0EnergyResolventPencil (N : ℕ) [NeZero N] (z : ℂ) :
    gamma0EnergySpace N →L[ℂ] gamma0EnergySpace N :=
  ContinuousLinearMap.id ℂ (gamma0EnergySpace N)-
    (z+1) • ((gamma0EnergyMassAdjoint N).comp (gamma0EnergyInclusion N))

theorem gamma0EnergyResolventPencil_inner (N : ℕ) [NeZero N] (z : ℂ)
    (v u : gamma0EnergySpace N) :
    inner ℂ v (gamma0EnergyResolventPencil N z u)=
      inner ℂ (gamma0EnergyGradient N v) (gamma0EnergyGradient N u)-
        z*inner ℂ (gamma0EnergyInclusion N v) (gamma0EnergyInclusion N u) := by
  change inner ℂ v (u-(z+1) • gamma0EnergyMassAdjoint N (gamma0EnergyInclusion N u))=_
  have he := inner_sub_right (𝕜 := ℂ) v u ((z+1) • gamma0EnergyMassAdjoint N (gamma0EnergyInclusion N u))
  rw [he,inner_smul_right (𝕜 := ℂ) (E := gamma0EnergySpace N),gamma0EnergyMassAdjoint_inner,
    gamma0FormEnergy_inner]
  ring

theorem gamma0EnergyResolventPencil_coercive (N : ℕ) [NeZero N] (z : ℂ) (hz : z.re < ‖z‖)
    (u : gamma0EnergySpace N) :
    spectralResolventCoercivity z*‖u‖^(2:ℕ) ≤
      (inner ℂ u ((spectralResolventRotation z • gamma0EnergyResolventPencil N z) u)).re := by
  change spectralResolventCoercivity z*‖u‖^(2:ℕ) ≤
    (inner ℂ u (spectralResolventRotation z • gamma0EnergyResolventPencil N z u)).re
  rw [inner_smul_right (𝕜 := ℂ) (E := gamma0EnergySpace N),gamma0EnergyResolventPencil_inner,
    inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
  have hrot : (spectralResolventRotation z*((‖gamma0EnergyGradient N u‖:ℂ)^(2:ℕ)-
      z*(‖gamma0EnergyInclusion N u‖:ℂ)^(2:ℕ))).re=
      (1-z.re/‖z‖)*‖gamma0EnergyGradient N u‖^(2:ℕ)+(‖z‖-z.re)*‖gamma0EnergyInclusion N u‖^(2:ℕ) := by
    simpa only [Complex.ofReal_pow] using
      spectralResolventRotation_energy z hz (‖gamma0EnergyGradient N u‖^(2:ℕ)) (‖gamma0EnergyInclusion N u‖^(2:ℕ))
  have hg := mul_nonneg (sub_nonneg.mpr (min_le_left
    (1-z.re/‖z‖) (‖z‖-z.re))) (sq_nonneg ‖gamma0EnergyGradient N u‖)
  have hm := mul_nonneg (sub_nonneg.mpr (min_le_right
    (1-z.re/‖z‖) (‖z‖-z.re))) (sq_nonneg ‖gamma0EnergyInclusion N u‖)
  have hbound : spectralResolventCoercivity z*‖u‖^(2:ℕ) ≤
      (1-z.re/‖z‖)*‖gamma0EnergyGradient N u‖^(2:ℕ)+
        (‖z‖-z.re)*‖gamma0EnergyInclusion N u‖^(2:ℕ) := by
    rw [gamma0Energy_norm_sq]
    unfold spectralResolventCoercivity
    nlinarith
  exact hbound.trans_eq hrot.symm

def gamma0EnergyRotatedEquiv (N : ℕ) [NeZero N] (z : ℂ) (hz : z.re < ‖z‖) :
    gamma0EnergySpace N ≃L[ℂ] gamma0EnergySpace N :=
  OAI.CoulombAtom.coerciveEquiv (V := gamma0EnergySpace N) (spectralResolventRotation z • gamma0EnergyResolventPencil N z)
    (spectralResolventCoercivity_pos z hz) (gamma0EnergyResolventPencil_coercive N z hz)

def gamma0AmbientWeakResolvent (N : ℕ) [NeZero N] (z : ℂ) (hz : z.re < ‖z‖) :
    Gamma0RegionL2 N →L[ℂ] gamma0EnergySpace N :=
  (gamma0EnergyRotatedEquiv N z hz).symm.toContinuousLinearMap.comp
    (spectralResolventRotation z • gamma0EnergyMassAdjoint N)

def gamma0AmbientResolvent (N : ℕ) [NeZero N] (z : ℂ) (hz : z.re < ‖z‖) :
    Gamma0RegionL2 N →L[ℂ] Gamma0RegionL2 N :=
  (gamma0EnergyInclusion N).comp (gamma0AmbientWeakResolvent N z hz)

theorem gamma0AmbientWeakResolvent_pencil (N : ℕ) [NeZero N] (z : ℂ) (hz : z.re < ‖z‖)
    (F : Gamma0RegionL2 N) :
    gamma0EnergyResolventPencil N z (gamma0AmbientWeakResolvent N z hz F)=gamma0EnergyMassAdjoint N F := by
  have he := (gamma0EnergyRotatedEquiv N z hz).apply_symm_apply
    (spectralResolventRotation z • gamma0EnergyMassAdjoint N F)
  change spectralResolventRotation z •
      gamma0EnergyResolventPencil N z (gamma0AmbientWeakResolvent N z hz F)=
        spectralResolventRotation z • gamma0EnergyMassAdjoint N F at he
  have h := congrArg (fun u : gamma0EnergySpace N => (spectralResolventRotation z)⁻¹ • u) he
  simpa only [smul_smul,inv_mul_cancel₀ (spectralResolventRotation_ne_zero z hz),one_smul] using h

theorem gamma0AmbientWeakResolvent_equation (N : ℕ) [NeZero N] (z : ℂ) (hz : z.re < ‖z‖)
    (F : Gamma0RegionL2 N) (v : gamma0EnergySpace N) :
    inner ℂ (gamma0EnergyGradient N v)
        (gamma0EnergyGradient N (gamma0AmbientWeakResolvent N z hz F))-
      z*inner ℂ (gamma0EnergyInclusion N v) (gamma0AmbientResolvent N z hz F)=
        inner ℂ (gamma0EnergyInclusion N v) F := by
  have h := congrArg (fun u : gamma0EnergySpace N => inner ℂ v u)
    (gamma0AmbientWeakResolvent_pencil N z hz F)
  rw [gamma0EnergyResolventPencil_inner,gamma0EnergyMassAdjoint_inner] at h
  exact h

theorem gamma0AmbientWeakResolvent_unique (N : ℕ) [NeZero N] (z : ℂ) (hz : z.re < ‖z‖)
    (F : Gamma0RegionL2 N) (u : gamma0EnergySpace N)
    (hu : ∀ v : gamma0EnergySpace N,
      inner ℂ (gamma0EnergyGradient N v) (gamma0EnergyGradient N u)-
        z*inner ℂ (gamma0EnergyInclusion N v) (gamma0EnergyInclusion N u)=
          inner ℂ (gamma0EnergyInclusion N v) F) :
    u=gamma0AmbientWeakResolvent N z hz F := by
  have he : gamma0EnergyResolventPencil N z u=gamma0EnergyMassAdjoint N F := by
    apply ext_inner_left ℂ
    intro v
    rw [gamma0EnergyResolventPencil_inner,gamma0EnergyMassAdjoint_inner]
    exact hu v
  apply (gamma0EnergyRotatedEquiv N z hz).injective
  change spectralResolventRotation z • gamma0EnergyResolventPencil N z u=
    spectralResolventRotation z • gamma0EnergyResolventPencil N z (gamma0AmbientWeakResolvent N z hz F)
  rw [he,gamma0AmbientWeakResolvent_pencil]

end ArtinMatthews
