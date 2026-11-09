module

public import ArtinMatthews.SpectralGamma0CuspActualExpansion


set_option backward.privateInPublic true
@[expose] public section

/-! Orthogonal cusp projection in the actual full mass space.  The complementary
term is retained explicitly; the cuspidal Hilbert basis is never promoted to a
basis of the full automorphic space. -/

noncomputable section
open Set Filter Topology
open scoped InnerProductSpace BigOperators

namespace ArtinMatthews

local instance cuspidalProjection_innerProduct (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := Gamma0RegionL2 N) (gamma0AllHeightCuspidalMassSpace N)

def gamma0CuspidalProjection (N : ℕ) [NeZero N] :
    Gamma0RegionL2 N →L[ℂ] gamma0AllHeightCuspidalMassSpace N :=
  (gamma0AllHeightCuspidalMassSpace N).orthogonalProjectionOnto

def gamma0NoncuspidalRemainder (N : ℕ) [NeZero N] :
    Gamma0RegionL2 N →L[ℂ] Gamma0RegionL2 N :=
  ContinuousLinearMap.id ℂ (Gamma0RegionL2 N) -
    (gamma0AllHeightCuspidalMassSpace N).subtypeL.comp (gamma0CuspidalProjection N)

theorem gamma0CuspidalProjection_norm_le (N : ℕ) [NeZero N] (f : Gamma0RegionL2 N) :
    ‖gamma0CuspidalProjection N f‖ ≤ ‖f‖ :=
  (gamma0AllHeightCuspidalMassSpace N).norm_orthogonalProjectionOnto_apply_le f

theorem gamma0CuspidalProjection_inner_right (N : ℕ) [NeZero N]
    (f : Gamma0RegionL2 N) (g : gamma0AllHeightCuspidalMassSpace N) :
    inner ℂ (gamma0CuspidalProjection N f) g = inner ℂ f g.val :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right g f

theorem gamma0CuspidalProjection_inner_left (N : ℕ) [NeZero N]
    (f : gamma0AllHeightCuspidalMassSpace N) (g : Gamma0RegionL2 N) :
    inner ℂ f (gamma0CuspidalProjection N g) = inner ℂ f.val g :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left f g

theorem gamma0NoncuspidalRemainder_orthogonal (N : ℕ) [NeZero N]
    (f : Gamma0RegionL2 N) (g : gamma0AllHeightCuspidalMassSpace N) :
    inner ℂ (gamma0NoncuspidalRemainder N f) g.val = 0 :=
  (gamma0AllHeightCuspidalMassSpace N).starProjection_inner_eq_zero f g.val g.property

theorem gamma0_mass_cuspidal_split (N : ℕ) [NeZero N] (f g : Gamma0RegionL2 N) :
    inner ℂ f g = inner ℂ (gamma0CuspidalProjection N f) (gamma0CuspidalProjection N g) +
      inner ℂ (gamma0NoncuspidalRemainder N f) (gamma0NoncuspidalRemainder N g) := by
  have hleft := gamma0NoncuspidalRemainder_orthogonal N f (gamma0CuspidalProjection N g)
  have hright : inner ℂ (gamma0CuspidalProjection N f).val (gamma0NoncuspidalRemainder N g) = 0 :=
    inner_eq_zero_symm.mpr (gamma0NoncuspidalRemainder_orthogonal N g (gamma0CuspidalProjection N f))
  have hs (v : Gamma0RegionL2 N) :
      (gamma0CuspidalProjection N v).val + gamma0NoncuspidalRemainder N v = v := by
    change (gamma0CuspidalProjection N v).val + (v - (gamma0CuspidalProjection N v).val) = v
    abel
  calc
    _ = inner ℂ ((gamma0CuspidalProjection N f).val + gamma0NoncuspidalRemainder N f)
        ((gamma0CuspidalProjection N g).val + gamma0NoncuspidalRemainder N g) := by rw [hs, hs]
    _ = _ := by
      rw [inner_add_left, inner_add_right, inner_add_right, hleft, hright]
      simp only [add_zero, zero_add, Submodule.coe_inner]

theorem gamma0CuspidalProjection_spectral_hasSum (N : ℕ) [NeZero N]
    (f g : Gamma0RegionL2 N) :
    HasSum (fun i : Gamma0AllHeightSpectralIndex N =>
      inner ℂ f (gamma0FullCuspidalSpectralBasis N i).val *
        inner ℂ (gamma0FullCuspidalSpectralBasis N i).val g)
      (inner ℂ (gamma0CuspidalProjection N f) (gamma0CuspidalProjection N g)) := by
  simpa only [gamma0CuspidalProjection_inner_right, gamma0CuspidalProjection_inner_left] using
    (gamma0FullCuspidalSpectralBasis N).hasSum_inner_mul_inner
      (gamma0CuspidalProjection N f) (gamma0CuspidalProjection N g)

theorem gamma0_mass_spectral_split (N : ℕ) [NeZero N] (f g : Gamma0RegionL2 N) :
    inner ℂ f g =
      (∑' i : Gamma0AllHeightSpectralIndex N,
        inner ℂ f (gamma0FullCuspidalSpectralBasis N i).val *
          inner ℂ (gamma0FullCuspidalSpectralBasis N i).val g) +
      inner ℂ (gamma0NoncuspidalRemainder N f) (gamma0NoncuspidalRemainder N g) := by
  rw [(gamma0CuspidalProjection_spectral_hasSum N f g).tsum_eq]
  exact gamma0_mass_cuspidal_split N f g

theorem gamma0CuspidalSpectral_finite_bessel (N : ℕ) [NeZero N]
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (f : Gamma0RegionL2 N) :
    ∑ i ∈ s, ‖inner ℂ (gamma0FullCuspidalSpectralBasis N i).val f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have hb := (gamma0FullCuspidalSpectralBasis N).orthonormal.sum_inner_products_le
    (s := s) (gamma0CuspidalProjection N f)
  simp only [gamma0CuspidalProjection_inner_left] at hb
  exact hb.trans (pow_le_pow_left₀ (norm_nonneg _) (gamma0CuspidalProjection_norm_le N f) 2)

end ArtinMatthews
