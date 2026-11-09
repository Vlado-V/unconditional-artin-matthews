module

public import ArtinMatthews.SpectralEisensteinSynthesisInjective


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Eisenstein analysis maps onto the full normalized channel
space. The Hilbert adjoint is isometric and is its right inverse. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

local instance channelSurjectivity_cuspInner (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜:=ℂ) (E:=Gamma0RegionL2 N) (gamma0AllHeightCuspidalMassSpace N)

theorem gamma0EisensteinAnalysis_norm_sq_atoms (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    ‖u‖^2=‖gamma0EisensteinAnalysis N u‖^2+
      ∑' l : Ici (0:ℝ),‖gamma0AmbientSpectralAtomVector N u (l:ℝ)‖^2 := by
  have hfull := gamma0AmbientEisenstein_spectral_pairing N u u
  have hatom := gamma0AmbientAtomPair_native_split N u u
  have h : inner ℂ u u=inner ℂ (gamma0EisensteinAnalysis N u) (gamma0EisensteinAnalysis N u)+
      gamma0AmbientAtomPair N u u := by linear_combination hfull-hatom
  rw [gamma0AmbientAtomPair_diagonal] at h
  have hr := congrArg Complex.re h
  rw [Complex.add_re,Complex.ofReal_re,
    show (inner ℂ u u).re=‖u‖^2 from inner_self_eq_norm_sq (𝕜:=ℂ) u,
    show (inner ℂ (gamma0EisensteinAnalysis N u) (gamma0EisensteinAnalysis N u)).re=
      ‖gamma0EisensteinAnalysis N u‖^2 from inner_self_eq_norm_sq (𝕜:=ℂ) _] at hr
  exact hr

theorem gamma0EisensteinAnalysis_cuspidal_zero (N : ℕ) [NeZero N]
    (u : gamma0AllHeightCuspidalMassSpace N) : gamma0EisensteinAnalysis N u.val=0 := by
  have h := gamma0EisensteinAnalysis_norm_sq_atoms N u.val
  rw [gamma0AmbientAtomNormSq_sum_split] at h
  have hp : gamma0CuspidalProjection N u.val=u :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self u
  rw [hp] at h
  have hn : 0≤∑' l : Ici (0:ℝ),‖gamma0NoncuspidalRemainder N
      (gamma0AmbientSpectralAtomVector N u.val (l:ℝ))‖^2 := tsum_nonneg (fun _ => sq_nonneg _)
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  have hval : ‖u.val‖=‖u‖ := rfl
  rw [hval] at h
  nlinarith [sq_nonneg ‖gamma0EisensteinAnalysis N u.val‖]

theorem gamma0EisensteinAnalysis_eigen_zero (N : ℕ) [NeZero N]
    (l : ℝ) (hl : 0≤l) (u : Gamma0RegionL2 N) (hu : u∈gamma0AmbientEnergyEigenspace N l) :
    gamma0EisensteinAnalysis N u=0 := by
  have hp : gamma0AmbientSpectralAtomVector N u l=u := by
    rw [gamma0AmbientSpectralAtomVector_eq_projection]
    exact Submodule.starProjection_eq_self_iff.mpr hu
  have hterm : ‖u‖^2≤∑' k : Ici (0:ℝ),‖gamma0AmbientSpectralAtomVector N u (k:ℝ)‖^2 := by
    have h := (gamma0AmbientAtomNormSq_summable N u).le_tsum ⟨l,hl⟩ (fun _ _ => sq_nonneg _)
    simpa only [hp] using h
  have h := gamma0EisensteinAnalysis_norm_sq_atoms N u
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  nlinarith [sq_nonneg ‖gamma0EisensteinAnalysis N u‖]

theorem gamma0EisensteinAnalysis_residual_zero (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    gamma0EisensteinAnalysis N (gamma0ResidualProjection N u)=0 := by
  rw [gamma0ResidualProjection,sum_apply,map_sum]
  apply Finset.sum_eq_zero
  intro l _
  exact gamma0EisensteinAnalysis_eigen_zero N l l.property _ (gamma0AmbientResidualProjection_mem N l u).1

theorem spectralAdjoint_projection_zero {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] K) (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (hA : ∀ u∈U,A u=0) (v : K) : U.starProjection (A.adjoint v)=0 := by
  let p := U.starProjection (A.adjoint v)
  have hp : p∈U := U.starProjection_apply_mem _
  have hself : U.starProjection p=p := Submodule.starProjection_eq_self_iff.mpr hp
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  have hi := U.inner_starProjection_left_eq_right p (A.adjoint v)
  rw [hself] at hi
  change inner ℂ p p=0
  rw [← hi,ContinuousLinearMap.adjoint_inner_right,hA p hp,inner_zero_left]

theorem gamma0EisensteinSynthesis_cuspidal_projection_zero (N : ℕ) [NeZero N]
    (v : Gamma0EisensteinSpectralSpace N) :
    (gamma0CuspidalProjection N ((gamma0EisensteinAnalysis N).adjoint v)).val=0 := by
  change (gamma0AllHeightCuspidalMassSpace N).starProjection ((gamma0EisensteinAnalysis N).adjoint v)=0
  exact spectralAdjoint_projection_zero (gamma0EisensteinAnalysis N) _
    (fun u hu => gamma0EisensteinAnalysis_cuspidal_zero N ⟨u,hu⟩) v

theorem gamma0EisensteinSynthesis_residual_projection_zero (N : ℕ) [NeZero N]
    (v : Gamma0EisensteinSpectralSpace N) :
    gamma0ResidualProjection N ((gamma0EisensteinAnalysis N).adjoint v)=0 := by
  rw [gamma0ResidualProjection,sum_apply]
  apply Finset.sum_eq_zero
  intro l _
  rw [gamma0AmbientResidualProjection_eq_orthogonalProjection]
  exact spectralAdjoint_projection_zero (gamma0EisensteinAnalysis N)
    (gamma0ResidualEnergyEigenspace N l)
    (fun u hu => gamma0EisensteinAnalysis_eigen_zero N l l.property u hu.1) v

theorem gamma0EisensteinAnalysis_synthesis (N : ℕ) [NeZero N] (v : Gamma0EisensteinSpectralSpace N) :
    gamma0EisensteinAnalysis N ((gamma0EisensteinAnalysis N).adjoint v)=v := by
  have h := gamma0AmbientEisenstein_resolution N ((gamma0EisensteinAnalysis N).adjoint v)
  rw [gamma0EisensteinSynthesis_cuspidal_projection_zero,gamma0EisensteinSynthesis_residual_projection_zero,
    zero_add,zero_add] at h
  exact ((gamma0EisensteinSynthesis_injective N) h).symm

theorem gamma0EisensteinAnalysis_surjective (N : ℕ) [NeZero N] :
    Function.Surjective (gamma0EisensteinAnalysis N) :=
  fun v => ⟨(gamma0EisensteinAnalysis N).adjoint v,gamma0EisensteinAnalysis_synthesis N v⟩

theorem gamma0EisensteinSynthesis_norm (N : ℕ) [NeZero N] (v : Gamma0EisensteinSpectralSpace N) :
    ‖(gamma0EisensteinAnalysis N).adjoint v‖=‖v‖ := by
  have h : inner ℂ ((gamma0EisensteinAnalysis N).adjoint v) ((gamma0EisensteinAnalysis N).adjoint v)=
      inner ℂ v v := by
    rw [ContinuousLinearMap.adjoint_inner_left,gamma0EisensteinAnalysis_synthesis]
  have hr := congrArg Complex.re h
  rw [show (inner ℂ ((gamma0EisensteinAnalysis N).adjoint v) ((gamma0EisensteinAnalysis N).adjoint v)).re=
      ‖(gamma0EisensteinAnalysis N).adjoint v‖^2 from inner_self_eq_norm_sq (𝕜:=ℂ) _,
    show (inner ℂ v v).re=‖v‖^2 from inner_self_eq_norm_sq (𝕜:=ℂ) _] at hr
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hr

def gamma0EisensteinSynthesisIsometry (N : ℕ) [NeZero N] :
    Gamma0EisensteinSpectralSpace N →ₗᵢ[ℂ] Gamma0RegionL2 N :=
  ⟨(gamma0EisensteinAnalysis N).adjoint.toLinearMap,gamma0EisensteinSynthesis_norm N⟩

end ArtinMatthews
