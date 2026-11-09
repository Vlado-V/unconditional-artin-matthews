module

public import ArtinMatthews.SpectralStoneCuspidalAtoms
public import ArtinMatthews.SpectralAmbientCriticalEigenmodes


set_option backward.privateInPublic true
@[expose] public section

/-! Actual residual eigenspace projections and their absolutely
summable products. Residual energies are below the continuous threshold. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

def gamma0AmbientResidualProjection (N : ℕ) [NeZero N] (l : ℝ) :
    Gamma0RegionL2 N →L[ℂ] Gamma0RegionL2 N :=
  (gamma0NoncuspidalRemainder N).comp (gamma0AmbientEnergyEigenspace N l).starProjection

theorem gamma0AmbientResidualProjection_eq (N : ℕ) [NeZero N] (l : ℝ) (u : Gamma0RegionL2 N) :
    gamma0AmbientResidualProjection N l u=
      gamma0NoncuspidalRemainder N (gamma0AmbientSpectralAtomVector N u l) := by
  rw [gamma0AmbientResidualProjection,ContinuousLinearMap.comp_apply,gamma0AmbientSpectralAtomVector_eq_projection]

theorem gamma0AmbientResidualProjection_zero_of_critical (N : ℕ) [NeZero N]
    (l : ℝ) (hl : (1/4:ℝ)≤l) (u : Gamma0RegionL2 N) :
    gamma0AmbientResidualProjection N l u=0 := by
  rw [gamma0AmbientResidualProjection_eq]
  exact gamma0NoncuspidalRemainder_atom_zero_of_critical N l hl u

theorem gamma0StoneResidualPair_terms_summable (N : ℕ) [NeZero N] (u v : Gamma0RegionL2 N) :
    Summable (fun l : Ici (0:ℝ) =>
      inner ℂ (gamma0AmbientResidualProjection N (l:ℝ) u) (gamma0AmbientResidualProjection N (l:ℝ) v)) := by
  let b (u : Gamma0RegionL2 N) (l : Ici (0:ℝ)) := gamma0AmbientResidualProjection N (l:ℝ) u
  have hs (w : Gamma0RegionL2 N) : Summable (fun l : Ici (0:ℝ) => ‖b w l‖^2) := by
    simpa only [b,gamma0AmbientResidualProjection_eq] using gamma0AmbientResidualAtomNormSq_summable N w
  apply ((hs u).add (hs v)).of_norm_bounded
  intro l
  refine (norm_inner_le_norm (𝕜:=ℂ) (b u l) (b v l)).trans ?_
  nlinarith [sq_nonneg (‖b u l‖-‖b v l‖),sq_nonneg ‖b u l‖,sq_nonneg ‖b v l‖]

def gamma0StoneResidualPair (N : ℕ) [NeZero N] (u v : Gamma0RegionL2 N) : ℂ :=
  ∑' l : Ici (0:ℝ),inner ℂ (gamma0AmbientResidualProjection N (l:ℝ) u) (gamma0AmbientResidualProjection N (l:ℝ) v)

theorem gamma0StoneResidualPair_add_right (N : ℕ) [NeZero N] (u v w : Gamma0RegionL2 N) :
    gamma0StoneResidualPair N u (v+w)=gamma0StoneResidualPair N u v+gamma0StoneResidualPair N u w := by
  simp only [gamma0StoneResidualPair,map_add,inner_add_right]
  exact (gamma0StoneResidualPair_terms_summable N u v).tsum_add (gamma0StoneResidualPair_terms_summable N u w)

theorem gamma0StoneResidualPair_smul_right (N : ℕ) [NeZero N] (c : ℂ) (u v : Gamma0RegionL2 N) :
    gamma0StoneResidualPair N u (c • v)=c*gamma0StoneResidualPair N u v := by
  simp only [gamma0StoneResidualPair,map_smul,inner_smul_right]
  exact tsum_mul_left

theorem gamma0StoneResidualPair_conj (N : ℕ) [NeZero N] (u v : Gamma0RegionL2 N) :
    (starRingEnd ℂ) (gamma0StoneResidualPair N u v)=gamma0StoneResidualPair N v u := by
  have h := Complex.conjCLE.toContinuousLinearMap.map_tsum (gamma0StoneResidualPair_terms_summable N u v)
  change (starRingEnd ℂ) (gamma0StoneResidualPair N u v)=
    ∑' l : Ici (0:ℝ),(starRingEnd ℂ)
      (inner ℂ (gamma0AmbientResidualProjection N (l:ℝ) u) (gamma0AmbientResidualProjection N (l:ℝ) v)) at h
  simp only [inner_conj_symm] at h
  exact h

theorem gamma0StoneResidualPair_diagonal (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    gamma0StoneResidualPair N u u=
      ((∑' l : Ici (0:ℝ),‖gamma0NoncuspidalRemainder N (gamma0AmbientSpectralAtomVector N u (l:ℝ))‖^2):ℝ) := by
  have h := Complex.ofRealCLM.map_tsum (gamma0AmbientResidualAtomNormSq_summable N u)
  rw [gamma0StoneResidualPair]
  change (((∑' l : Ici (0:ℝ),‖gamma0NoncuspidalRemainder N
    (gamma0AmbientSpectralAtomVector N u (l:ℝ))‖^2):ℝ):ℂ) =
      (∑' l : Ici (0:ℝ),((‖gamma0NoncuspidalRemainder N
        (gamma0AmbientSpectralAtomVector N u (l:ℝ))‖^2:ℝ):ℂ)) at h
  rw [h]
  apply tsum_congr
  intro l
  rw [inner_self_eq_norm_sq_to_K (𝕜:=ℂ),gamma0AmbientResidualProjection_eq,Complex.ofReal_pow]
  rfl

end ArtinMatthews
