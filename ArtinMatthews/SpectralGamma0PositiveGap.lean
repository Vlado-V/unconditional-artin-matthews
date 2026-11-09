module

public import ArtinMatthews.SpectralGamma0GradientCuspResidual
public import ArtinMatthews.SpectralGamma0CuspMassFaithful
public import ArtinMatthews.SpectralGamma0SpectralCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! Strict positivity and a fixed-level positive gap for the actual cuspidal
gradient spectrum, using the actual form domain and finite spectral cutoffs. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

local instance positiveGap_massInner (N : ℕ) [NeZero N] :
    Inner ℂ (gamma0AllHeightEnergyMassSpace N) :=
  (gamma0AllHeightEnergyMassSpace_innerProductSpace N).toInner

theorem gamma0AllHeightMeanZeroEnergy_mass_eq_zero_of_gradient_eq_zero
    (N : ℕ) [NeZero N] (u : gamma0AllHeightMeanZeroEnergy N)
    (hu : gamma0EnergyGradient N u.val = 0) :
    gamma0EnergyInclusion N u.val = 0 := by
  apply gamma0Mass_eq_zero_of_low_cusps_eq_zero N
  intro r
  rw [gamma0CuspMassRestriction_energy]
  exact gamma0AllHeightMeanZeroEnergy_restriction_eq_zero_of_gradient_eq_zero N u hu r
    (1/2) (by norm_num)

theorem gamma0AllHeightMeanZeroEnergy_eq_zero_of_gradient_eq_zero
    (N : ℕ) [NeZero N] (u : gamma0AllHeightMeanZeroEnergy N)
    (hu : gamma0EnergyGradient N u.val = 0) : u = 0 := by
  have hm := gamma0AllHeightMeanZeroEnergy_mass_eq_zero_of_gradient_eq_zero N u hu
  have hn := gamma0Energy_norm_sq N u.val
  rw [hm,hu] at hn
  simp only [norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),add_zero] at hn
  apply Subtype.ext
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

theorem gamma0AllHeightGradientSpectralValue_pos (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) : 0 < gamma0AllHeightGradientSpectralValue N i := by
  by_contra hn
  have hzero : gamma0AllHeightGradientSpectralValue N i = 0 :=
    le_antisymm (le_of_not_gt hn) (gamma0AllHeightGradientSpectralValue_nonneg N i)
  have he := gamma0AllHeightSpectralEnergy_gradient N i (gamma0AllHeightSpectralEnergy N i)
  rw [hzero,Complex.ofReal_zero,zero_mul] at he
  have hg : gamma0EnergyGradient N (gamma0AllHeightSpectralEnergy N i).val = 0 :=
    (inner_self_eq_zero (𝕜 := ℂ)).mp he
  have hm := gamma0AllHeightMeanZeroEnergy_mass_eq_zero_of_gradient_eq_zero N
    (gamma0AllHeightSpectralEnergy N i) hg
  have hb : gamma0AllHeightSpectralBasis N i = 0 := by
    apply Subtype.ext
    have h := congrArg Subtype.val (gamma0AllHeightSpectralEnergy_mass N i)
    exact h.symm.trans hm
  have hu := (gamma0AllHeightSpectralBasis N).orthonormal.norm_eq_one i
  rw [hb,norm_zero] at hu
  exact zero_ne_one hu

theorem gamma0AllHeightGradientSpectralGap (N : ℕ) [NeZero N] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i : Gamma0AllHeightSpectralIndex N,
      δ ≤ gamma0AllHeightGradientSpectralValue N i := by
  classical
  let s : Finset ℝ := insert 1 ((gamma0AllHeightGradientSpectralCutoff N 1).image
    (gamma0AllHeightGradientSpectralValue N))
  have hs : s.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs,?_,?_⟩
  · apply (Finset.lt_min'_iff _ _).mpr
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact zero_lt_one
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact gamma0AllHeightGradientSpectralValue_pos N i
  · intro i
    by_cases hi : gamma0AllHeightGradientSpectralValue N i ≤ 1
    · apply Finset.min'_le s _
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨i,(mem_gamma0AllHeightGradientSpectralCutoff N 1 i).mpr hi,rfl⟩)
    · exact (Finset.min'_le s 1 (Finset.mem_insert_self _ _)).trans (le_of_not_ge hi)

end ArtinMatthews
