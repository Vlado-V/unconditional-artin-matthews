module

public import ArtinMatthews.SpectralEnergyTest


set_option backward.privateInPublic true
@[expose] public section

/-! Energy tests on the genuine finite residual spectrum. Each retained
term is the actual orthogonal residual eigenspace projection. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace ArtinMatthews

theorem gamma0ResidualProjection_pair (N : ℕ) [NeZero N] (l : Ici (0:ℝ))
    (u v : Gamma0RegionL2 N) :
    inner ℂ u (gamma0AmbientResidualProjection N l v)=
      inner ℂ (gamma0AmbientResidualProjection N l u) (gamma0AmbientResidualProjection N l v) := by
  let U := gamma0ResidualEnergyEigenspace N l
  rw [gamma0AmbientResidualProjection_eq_orthogonalProjection,gamma0AmbientResidualProjection_eq_orthogonalProjection]
  have hi := U.inner_starProjection_left_eq_right u (U.starProjection v)
  rw [Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem v)] at hi
  exact hi.symm

def gamma0ResidualTestOperator (N : ℕ) [NeZero N] (h : SpectralEnergyTest) :
    Gamma0RegionL2 N →L[ℂ] Gamma0RegionL2 N :=
  ∑ l∈gamma0ResidualEnergyWindow N,h l • gamma0AmbientResidualProjection N l

theorem gamma0ResidualTestOperator_pair (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (u v : Gamma0RegionL2 N) :
    inner ℂ u (gamma0ResidualTestOperator N h v)=
      ∑ l∈gamma0ResidualEnergyWindow N,h l*
        ∑ j,inner ℂ u (gamma0ResidualEigenbasis N l j).val*
          inner ℂ (gamma0ResidualEigenbasis N l j).val v := by
  rw [gamma0ResidualTestOperator,sum_apply,inner_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [smul_apply,inner_smul_right,gamma0ResidualProjection_pair,gamma0AmbientResidualProjection_basis_pairing]

theorem gamma0ResidualTestOperator_green (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    gamma0ResidualTestOperator N spectralGreenEnergyTest u=gamma0Green N (gamma0ResidualProjection N u) := by
  rw [gamma0ResidualTestOperator,sum_apply,gamma0ResidualProjection,sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [smul_apply,spectralGreenEnergyTest_apply,gamma0EnergyGreenWeight_eq_real]
  exact ((mem_gamma0AmbientEnergyEigenspace_iff N l _).mp (gamma0AmbientResidualProjection_mem N l u).1).symm

end ArtinMatthews
