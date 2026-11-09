module

public import ArtinMatthews.SpectralResidualFiniteResolution
public import Mathlib.Analysis.InnerProductSpace.PiL2


set_option backward.privateInPublic true
@[expose] public section

/-! Honest finite residual eigenvectors in the ambient Hilbert space.
Their finite orthonormal sums replace the retained projections exactly. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem gamma0ResidualEnergyEigenspace_closed (N : ℕ) [NeZero N] (l : ℝ) :
    IsClosed (gamma0ResidualEnergyEigenspace N l : Set (Gamma0RegionL2 N)) :=
  (gamma0AmbientEnergyEigenspace_closed N l).inter (gamma0AllHeightCuspidalMassSpace N).isClosed_orthogonal

instance gamma0ResidualEnergyEigenspace_complete (N : ℕ) [NeZero N] (l : ℝ) :
    CompleteSpace (gamma0ResidualEnergyEigenspace N l) :=
  (gamma0ResidualEnergyEigenspace_closed N l).isComplete.completeSpace_coe

theorem gamma0AmbientResidualProjection_eq_orthogonalProjection (N : ℕ) [NeZero N]
    (l : ℝ) (u : Gamma0RegionL2 N) :
    gamma0AmbientResidualProjection N l u=(gamma0ResidualEnergyEigenspace N l).starProjection u := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (gamma0AmbientResidualProjection_mem N l u)
  intro w hw
  let a := gamma0AmbientSpectralAtomVector N u l
  let p := gamma0CuspidalProjection N a
  have h1 : inner ℂ (u-a) w=0 := inner_eq_zero_symm.mpr
    (gamma0AmbientSpectralAtomVector_orthogonal N u w l ((mem_gamma0AmbientEnergyEigenspace_iff N l w).mp hw.1))
  have h2 : inner ℂ p.val w=0 := hw.2 p.val p.property
  rw [gamma0AmbientResidualProjection_eq]
  change inner ℂ (u-(a-p.val)) w=0
  rw [show u-(a-p.val)=(u-a)+p.val by abel,inner_add_left,h1,h2,add_zero]

def gamma0ResidualEigenbasis (N : ℕ) [NeZero N] (l : Ici (0:ℝ)) :
    OrthonormalBasis (Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l)))
      ℂ (gamma0ResidualEnergyEigenspace N l) := by
  let _ : FiniteDimensional ℂ (gamma0ResidualEnergyEigenspace N l) :=
    gamma0ResidualEnergyEigenspace_finiteDimensional N l l.property
  exact stdOrthonormalBasis ℂ (gamma0ResidualEnergyEigenspace N l)

theorem gamma0ResidualEigenbasis_green (N : ℕ) [NeZero N] (l : Ici (0:ℝ))
    (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l))) :
    gamma0Green N (gamma0ResidualEigenbasis N l j).val=
      ((((l:ℝ)+1)⁻¹:ℝ):ℂ) • (gamma0ResidualEigenbasis N l j).val :=
  (mem_gamma0AmbientEnergyEigenspace_iff N l _).mp (gamma0ResidualEigenbasis N l j).property.1

theorem gamma0ResidualEigenbasis_cusp_orthogonal (N : ℕ) [NeZero N] (l : Ici (0:ℝ))
    (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l)))
    (w : gamma0AllHeightCuspidalMassSpace N) :
    inner ℂ w.val (gamma0ResidualEigenbasis N l j).val=0 :=
  (gamma0ResidualEigenbasis N l j).property.2 w.val w.property

theorem gamma0ResidualEigenbasis_energy_pencil (N : ℕ) [NeZero N] (l : Ici (0:ℝ))
    (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l))) :
    ∃ u : gamma0EnergySpace N,gamma0EnergyInclusion N u=(gamma0ResidualEigenbasis N l j).val ∧
      gamma0EnergyResolventPencil N ((l:ℝ):ℂ) u=0 :=
  gamma0AmbientEnergyEigenspace_energy_pencil N l l.property _ (gamma0ResidualEigenbasis N l j).property.1

theorem gamma0AmbientResidualProjection_basis_pairing (N : ℕ) [NeZero N] (l : Ici (0:ℝ))
    (u v : Gamma0RegionL2 N) :
    inner ℂ (gamma0AmbientResidualProjection N l u) (gamma0AmbientResidualProjection N l v)=
      ∑ j,inner ℂ u (gamma0ResidualEigenbasis N l j).val*
        inner ℂ (gamma0ResidualEigenbasis N l j).val v := by
  let K := gamma0ResidualEnergyEigenspace N l
  have hu : (K.orthogonalProjectionOnto u).val=gamma0AmbientResidualProjection N l u :=
    (gamma0AmbientResidualProjection_eq_orthogonalProjection N l u).symm
  have hv : (K.orthogonalProjectionOnto v).val=gamma0AmbientResidualProjection N l v :=
    (gamma0AmbientResidualProjection_eq_orthogonalProjection N l v).symm
  have h := (gamma0ResidualEigenbasis N l).sum_inner_mul_inner (K.orthogonalProjectionOnto u) (K.orthogonalProjectionOnto v)
  have hleft (j : Fin (Module.finrank ℂ K)) :
      inner ℂ (K.orthogonalProjectionOnto u) (gamma0ResidualEigenbasis N l j)=
        inner ℂ u (gamma0ResidualEigenbasis N l j).val :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right _ u
  have hright (j : Fin (Module.finrank ℂ K)) :
      inner ℂ (gamma0ResidualEigenbasis N l j) (K.orthogonalProjectionOnto v)=
        inner ℂ (gamma0ResidualEigenbasis N l j).val v :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ v
  have hs : (∑ i,inner ℂ (K.orthogonalProjectionOnto u) (gamma0ResidualEigenbasis N l i)*
      inner ℂ (gamma0ResidualEigenbasis N l i) (K.orthogonalProjectionOnto v))=
      ∑ i,inner ℂ u (gamma0ResidualEigenbasis N l i).val*
        inner ℂ (gamma0ResidualEigenbasis N l i).val v := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hleft i,hright i]
  rw [hs] at h
  have hi : inner ℂ (K.orthogonalProjectionOnto u) (K.orthogonalProjectionOnto v)=
      inner ℂ (gamma0AmbientResidualProjection N l u) (gamma0AmbientResidualProjection N l v) := by
    change inner ℂ (K.orthogonalProjectionOnto u).val (K.orthogonalProjectionOnto v).val=_
    rw [hu,hv]
  rw [hi] at h
  exact h.symm

theorem gamma0StoneResidualPair_eq_finite_eigenbasis (N : ℕ) [NeZero N] (u v : Gamma0RegionL2 N) :
    gamma0StoneResidualPair N u v=
      ∑ l∈gamma0ResidualEnergyWindow N,
        ∑ j,inner ℂ u (gamma0ResidualEigenbasis N l j).val*
          inner ℂ (gamma0ResidualEigenbasis N l j).val v := by
  rw [gamma0StoneResidualPair_eq_finite]
  apply Finset.sum_congr rfl
  intro l _
  exact gamma0AmbientResidualProjection_basis_pairing N l u v

end ArtinMatthews
