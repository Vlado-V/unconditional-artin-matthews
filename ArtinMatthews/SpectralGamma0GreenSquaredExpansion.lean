module

public import ArtinMatthews.SpectralGamma0GreenSpectralBound
public import Mathlib.Order.Filter.AtTopBot.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! Full spectral expansions of the actual cuspidal Green operator and its square. -/
noncomputable section
open Set Filter
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

local instance greenSquaredExpansion_inner (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := Gamma0RegionL2 N) _

theorem gamma0CuspidalGreen_basis_eigen (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    gamma0CuspidalGreen N (gamma0FullCuspidalSpectralBasis N i) =
      i.1 • gamma0FullCuspidalSpectralBasis N i := by
  apply Subtype.ext
  exact gamma0FullCuspidalSpectralBasis_eigen N i

theorem gamma0CuspidalGreen_basis_coefficient (N : ℕ) [NeZero N]
    (f : gamma0AllHeightCuspidalMassSpace N) (i : Gamma0AllHeightSpectralIndex N) :
    (gamma0FullCuspidalSpectralBasis N).repr (gamma0CuspidalGreen N f) i =
      (i.1.re : ℂ) * (gamma0FullCuspidalSpectralBasis N).repr f i := by
  rw [HilbertBasis.repr_apply_apply,HilbertBasis.repr_apply_apply]
  change inner ℂ (gamma0FullCuspidalSpectralBasis N i).val (gamma0Green N f.val) =
    (i.1.re : ℂ) * inner ℂ (gamma0FullCuspidalSpectralBasis N i).val f.val
  have he := gamma0Green_symmetric N (gamma0FullCuspidalSpectralBasis N i).val f.val
  change inner ℂ (gamma0Green N (gamma0FullCuspidalSpectralBasis N i).val) f.val =
    inner ℂ (gamma0FullCuspidalSpectralBasis N i).val (gamma0Green N f.val) at he
  rw [gamma0FullCuspidalSpectralBasis_eigen,inner_smul_left,
    ← gamma0AllHeightSpectralValue_real N i] at he
  simpa only [Complex.conj_ofReal] using he.symm

theorem gamma0CuspidalGreen_hasSum (N : ℕ) [NeZero N]
    (f : gamma0AllHeightCuspidalMassSpace N) :
    HasSum (fun i : Gamma0AllHeightSpectralIndex N =>
      ((i.1.re : ℂ) * (gamma0FullCuspidalSpectralBasis N).repr f i) •
        gamma0FullCuspidalSpectralBasis N i) (gamma0CuspidalGreen N f) := by
  simpa only [gamma0CuspidalGreen_basis_coefficient] using
    (gamma0FullCuspidalSpectralBasis N).hasSum_repr (gamma0CuspidalGreen N f)

theorem gamma0CuspidalGreen_squared_hasSum (N : ℕ) [NeZero N]
    (f : gamma0AllHeightCuspidalMassSpace N) :
    HasSum (fun i : Gamma0AllHeightSpectralIndex N =>
      (((i.1.re : ℂ)^2) * (gamma0FullCuspidalSpectralBasis N).repr f i) •
        gamma0FullCuspidalSpectralBasis N i) (gamma0CuspidalGreen N (gamma0CuspidalGreen N f)) := by
  have h := gamma0CuspidalGreen_hasSum N (gamma0CuspidalGreen N f)
  simpa only [gamma0CuspidalGreen_basis_coefficient,pow_two,mul_assoc] using h

theorem gamma0CuspidalGreen_squared_pairing_hasSum (N : ℕ) [NeZero N]
    (f g : gamma0AllHeightCuspidalMassSpace N) :
    HasSum (fun i : Gamma0AllHeightSpectralIndex N =>
      (i.1.re : ℂ)^2 * star ((gamma0FullCuspidalSpectralBasis N).repr f i) *
        (gamma0FullCuspidalSpectralBasis N).repr g i)
      (inner ℂ f (gamma0CuspidalGreen N (gamma0CuspidalGreen N g))) := by
  have h := (gamma0FullCuspidalSpectralBasis N).hasSum_inner_mul_inner
    f (gamma0CuspidalGreen N (gamma0CuspidalGreen N g))
  have he (i : Gamma0AllHeightSpectralIndex N) :
      inner ℂ f (gamma0FullCuspidalSpectralBasis N i) *
        inner ℂ (gamma0FullCuspidalSpectralBasis N i) (gamma0CuspidalGreen N (gamma0CuspidalGreen N g)) =
      (i.1.re : ℂ)^2 * star ((gamma0FullCuspidalSpectralBasis N).repr f i) *
        (gamma0FullCuspidalSpectralBasis N).repr g i := by
    have hc : inner ℂ f (gamma0FullCuspidalSpectralBasis N i) =
        star ((gamma0FullCuspidalSpectralBasis N).repr f i) := by
      rw [HilbertBasis.repr_apply_apply]
      exact (inner_conj_symm f (gamma0FullCuspidalSpectralBasis N i)).symm
    rw [hc,← HilbertBasis.repr_apply_apply,gamma0CuspidalGreen_basis_coefficient,
      gamma0CuspidalGreen_basis_coefficient]
    ring
  simpa only [he] using h

theorem gamma0AllHeightGradientSpectralCutoff_tendsto (N : ℕ) [NeZero N] :
    Tendsto (gamma0AllHeightGradientSpectralCutoff N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone
  · intro R S hRS i hi
    exact (mem_gamma0AllHeightGradientSpectralCutoff N S i).mpr
      (((mem_gamma0AllHeightGradientSpectralCutoff N R i).mp hi).trans hRS)
  · intro i
    exact ⟨gamma0AllHeightGradientSpectralValue N i,
      (mem_gamma0AllHeightGradientSpectralCutoff N _ i).mpr le_rfl⟩

theorem gamma0CuspidalGreen_squared_pairing_cutoff_tendsto (N : ℕ) [NeZero N]
    (f g : gamma0AllHeightCuspidalMassSpace N) :
    Tendsto (fun R : ℝ => ∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R,
      (i.1.re : ℂ)^2 * star ((gamma0FullCuspidalSpectralBasis N).repr f i) *
        (gamma0FullCuspidalSpectralBasis N).repr g i) atTop
      (nhds (inner ℂ f (gamma0CuspidalGreen N (gamma0CuspidalGreen N g)))) :=
  (gamma0CuspidalGreen_squared_pairing_hasSum N f g).comp
    (gamma0AllHeightGradientSpectralCutoff_tendsto N)

end ArtinMatthews
