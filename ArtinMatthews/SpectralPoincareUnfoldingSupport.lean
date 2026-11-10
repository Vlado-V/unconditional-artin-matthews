module

public import ArtinMatthews.SpectralPoincareGamma0
public import Mathlib.NumberTheory.Modular
public import ArtinMatthews.SpectralCompactChartCover
public import ArtinMatthews.SpectralModularDensityPeriodization
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.MeasureTheory.Covering.Besicovitch


set_option backward.privateInPublic true
@[expose] public section

/-! Compact seeds have only finitely many contributing arithmetic translates
on an entire modular chart, including its unbounded cusp.  The finiteness is
proved from actual modular proper discontinuity and compact height control. -/

noncomputable section
open Set
open scoped MatrixGroups CompactlySupported Pointwise

namespace ArtinMatthews

theorem gamma0_compact_seed_fd_translates_finite (N : ℕ) (r : SL(2, ℤ))
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    {γ : CongruenceSubgroup.Gamma0 N |
      ∃ z ∈ ModularGroup.fd, (γ : SL(2, ℤ)) • (r⁻¹ • z) ∈ K}.Finite := by
  let ι : CongruenceSubgroup.Gamma0 N → SL(2, ℤ) := fun γ => r * (γ : SL(2, ℤ))⁻¹
  have hinj : Function.Injective ι := by
    intro γ η h
    apply Subtype.ext
    apply inv_injective
    exact mul_left_cancel h
  apply ((compact_modular_translates_meeting_fd_finite hK).preimage hinj.injOn).subset
  rintro γ ⟨z, hz, hγz⟩
  exact ⟨z, ⟨(γ : SL(2, ℤ)) • (r⁻¹ • z), hγz,
    by simp only [ι, mul_smul, inv_smul_smul, smul_inv_smul]⟩, hz⟩

/-- One actual finite arithmetic sum works on the complete standard modular
domain, rather than merely in a neighborhood of a point. -/
theorem gamma0PoincareSeed_fd_eq_sum (N : ℕ) [NeZero N]
    (ψ : C_c(UpperHalfPlane, ℂ)) (r : SL(2, ℤ)) :
    ∃ s : Finset (CongruenceSubgroup.Gamma0 N), ∀ z ∈ ModularGroup.fd,
      gamma0PoincareSeed N ψ (r⁻¹ • z) =
        ∑ γ ∈ s, ψ ((γ : SL(2, ℤ)) • (r⁻¹ • z)) := by
  classical
  let hf := gamma0_compact_seed_fd_translates_finite N r ψ.hasCompactSupport
  refine ⟨hf.toFinset, fun z hz => ?_⟩
  rw [gamma0PoincareSeed_eq_finsum]
  apply finsum_eq_sum_of_support_subset
  intro γ hγ
  exact hf.mem_toFinset.mpr ⟨z, hz, subset_tsupport ψ hγ⟩

end ArtinMatthews
