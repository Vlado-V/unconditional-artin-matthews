module

public import ArtinMatthews.SpectralClosedFormData


set_option backward.privateInPublic true
@[expose] public section

/-! The compact closed-form resolvent takes values in the actual energy
space before mass inclusion. This stronger meromorphic family is needed
to test its full, rather than truncated, weak defect. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace ArtinMatthews

section
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

def spectralRectangularSandwichLinear (J : E →L[ℂ] G) (K : F →L[ℂ] E) :
    (E →L[ℂ] E) →L[ℂ] (F →L[ℂ] G) :=
  (ContinuousLinearMap.compL ℂ F E G J).comp
    (ContinuousLinearMap.flip (E := E →L[ℂ] E) (F := F →L[ℂ] E) (G := F →L[ℂ] E)
      (σ₁₃ := RingHom.id ℂ) (σ₂₃ := RingHom.id ℂ) (ContinuousLinearMap.compL ℂ F E E) K)

end

namespace SpectralClosedFormData

section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def energyResolvent (d : SpectralClosedFormData V H) (z : ℂ) : H →L[ℂ] V :=
  d.subspace.subtypeL.comp (spectralClosedFormWeakResolvent d.subspace d.closed d.inclusion z)

theorem energyResolvent_mem (d : SpectralClosedFormData V H) (z : ℂ) (F : H) :
    d.energyResolvent z F ∈ d.subspace :=
  (spectralClosedFormWeakResolvent d.subspace d.closed d.inclusion z F).property

theorem energyResolvent_mass (d : SpectralClosedFormData V H) (z : ℂ) (F : H) :
    d.inclusion (d.energyResolvent z F)=d.resolvent z F := rfl

theorem energyResolvent_meromorphic (d : SpectralClosedFormData V H) :
    Meromorphic d.energyResolvent := by
  let _ : CompleteSpace d.subspace := d.closed.isComplete.completeSpace_coe
  intro z
  have h := spectralCompactFormPencil_inverse_meromorphicAt (spectralClosedFormGram d.subspace d.closed d.inclusion)
    (spectralClosedFormGram_compact d.subspace d.closed d.inclusion d.compact)
    (spectralClosedFormGram_symmetric d.subspace d.closed d.inclusion) z
  exact spectralMeromorphicAt_comp_clm (spectralRectangularSandwichLinear d.subspace.subtypeL
    (spectralClosedFormInclusion d.subspace d.inclusion).adjoint) h

theorem energyResolvent_analyticAt (d : SpectralClosedFormData V H) (z : ℂ) (hz : z∉d.exceptional) :
    AnalyticAt ℂ d.energyResolvent z := by
  let _ : CompleteSpace d.subspace := d.closed.isComplete.completeSpace_coe
  let T := spectralClosedFormGram d.subspace d.closed d.inclusion
  have hT := spectralClosedFormGram_compact d.subspace d.closed d.inclusion d.compact
  have hP : IsUnit (spectralCompactFormPencil T z) :=
    (spectralCompactFormPencil_isUnit_iff_notMem T hT z).mpr hz
  let B := spectralRectangularSandwichLinear d.subspace.subtypeL
    (spectralClosedFormInclusion d.subspace d.inclusion).adjoint
  exact (B.analyticAt _).comp (spectralOperatorPencilInverse_analyticAt T z hP)

theorem energyResolvent_equation (d : SpectralClosedFormData V H) (z : ℂ)
    (hz : z∉d.exceptional) (F : H) (v : V) (hv : v∈d.subspace) :
    inner ℂ v (d.energyResolvent z F)-(z+1)*inner ℂ (d.inclusion v) (d.inclusion (d.energyResolvent z F)) =
      inner ℂ (d.inclusion v) F :=
  spectralClosedFormWeakResolvent_equation d.subspace d.closed d.inclusion d.compact z hz F ⟨v,hv⟩

theorem energyResolvent_unique (d : SpectralClosedFormData V H) (z : ℂ)
    (hz : z∉d.exceptional) (F : H) (u : V) (hu : u∈d.subspace)
    (he : ∀ v : V, v∈d.subspace →
      inner ℂ v u-(z+1)*inner ℂ (d.inclusion v) (d.inclusion u)=inner ℂ (d.inclusion v) F) :
    u=d.energyResolvent z F := by
  let _ : CompleteSpace d.subspace := d.closed.isComplete.completeSpace_coe
  let T := spectralClosedFormGram d.subspace d.closed d.inclusion
  let K := spectralClosedFormInclusion d.subspace d.inclusion
  let P := spectralCompactFormPencil T z
  let w : d.subspace := ⟨u,hu⟩
  have hT := spectralClosedFormGram_compact d.subspace d.closed d.inclusion d.compact
  have hP : IsUnit P := (spectralCompactFormPencil_isUnit_iff_notMem T hT z).mpr hz
  have hw : P w=K.adjoint F := by
    apply ext_inner_left ℂ
    intro v
    change inner ℂ v (w-(z+1) • spectralFormMassGram K w)=inner ℂ v (K.adjoint F)
    rw [inner_sub_right,inner_smul_right,spectralFormMassGram_inner,K.adjoint_inner_right]
    exact he v.val v.property
  have hc := congrArg (fun A : d.subspace →L[ℂ] d.subspace => A w) (Ring.inverse_mul_cancel P hP)
  change Ring.inverse P (P w)=w at hc
  rw [hw] at hc
  exact congrArg Subtype.val hc.symm

end
end SpectralClosedFormData
end ArtinMatthews
